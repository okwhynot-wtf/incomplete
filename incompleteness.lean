/-
# Totality

The claim under examination is not aseity but completeness: that nothing lies
outside the system.  The argument is an underdetermination argument, not a
diagonal one.  There is no self-membership, no comprehension principle and no
fixed point.  The whole construction is `conceal`, which adds a single external
object leaving no internal trace.

Structure of the result:

  * `Complete` is not determined by appearances (`complete_not_appDetermined`).
  * Hence no system whose evidence is fixed by appearances knows it
    (`not_know_complete`), including a system for which it is true
    (`true_but_unknown`).
  * The converse claim is knowable when it holds (`know_incomplete`).
    Incompleteness is discoverable, completeness is not.
  * The one route to knowing completeness runs through `Transparent`
    (`KT_knows_complete`), and that premise is unknowable for the same reason
    (`not_know_transparent`).  This is the regress that replaces the diagonal.

The load-bearing assumption is that a traceless exterior is coherent.  It is
isolated in `Transparent` rather than hidden in an epistemic axiom.  Anyone who
rejects it is asserting that everything real shows up inside, which is the
completeness thesis itself.
-/

namespace Totality

/-- A world: an exterior domain together with the way each external thing shows
up in the interior `I`.  The interior is held fixed; worlds differ only in what
lies beyond it and how that beyond registers within. -/
structure World (I : Type) where
  Ext   : Type
  trace : Ext → I → Prop

variable {I : Type}

/-- How the world appears from inside: `i` is an interior mark of something
external. -/
def App (w : World I) (i : I) : Prop := ∃ e : w.Ext, w.trace e i

/-- Completeness: nothing lies outside. -/
def Complete (w : World I) : Prop := w.Ext → False

/-- Transparency: everything outside leaves some mark inside. -/
def Transparent (w : World I) : Prop := ∀ e : w.Ext, ∃ i, w.trace e i

/-- Two worlds are indiscernible when they present the same appearances. -/
def Indisc (w w' : World I) : Prop := ∀ i, App w i ↔ App w' i

/-- Knowledge as truth across all indiscernible worlds. -/
def K (w : World I) (P : World I → Prop) : Prop := ∀ w', Indisc w w' → P w'

theorem indisc_refl (w : World I) : Indisc w w := fun _ => Iff.rfl

theorem indisc_symm {w w' : World I} (h : Indisc w w') : Indisc w' w :=
  fun i => (h i).symm

theorem K_factive (w : World I) (P : World I → Prop) (h : K w P) : P w :=
  h w (indisc_refl w)

/-! ## Concealment

`conceal w` adds one external object that leaves no trace.  It presents exactly
the appearances `w` presents, and it is not complete. -/

def conceal (w : World I) : World I :=
  { Ext   := Sum w.Ext Unit,
    trace := fun e i =>
      match e with
      | Sum.inl e' => w.trace e' i
      | Sum.inr _  => False }

theorem indisc_conceal (w : World I) : Indisc w (conceal w) :=
  fun _ => Iff.intro
    (fun h => match h with | ⟨e, he⟩ => ⟨Sum.inl e, he⟩)
    (fun h => match h with
      | ⟨Sum.inl e, he⟩ => ⟨e, he⟩
      | ⟨Sum.inr _, he⟩ => he.elim)

theorem conceal_incomplete (w : World I) : ¬ Complete (conceal w) :=
  fun h => h (Sum.inr ())

theorem conceal_not_transparent (w : World I) : ¬ Transparent (conceal w) :=
  fun h => match h (Sum.inr ()) with | ⟨_, he⟩ => he

/-! ## Appearance-determination

A property is appearance-determined when indiscernible worlds agree on it.
Everything appearance-determined and true is known; `Complete` is not
appearance-determined, and that single fact carries the argument. -/

def AppDetermined (P : World I → Prop) : Prop :=
  ∀ w w', Indisc w w' → (P w ↔ P w')

theorem knows_all_appDetermined (w : World I) (P : World I → Prop)
    (hd : AppDetermined P) (hp : P w) : K w P :=
  fun w' hw => (hd w w' hw).mp hp

def emptyWorld (I : Type) : World I :=
  { Ext := Empty, trace := fun e _ => Empty.elim e }

theorem emptyWorld_complete (I : Type) : Complete (emptyWorld I) :=
  fun e => Empty.elim e

theorem complete_not_appDetermined (I : Type) :
    ¬ AppDetermined (I := I) Complete :=
  fun h =>
    conceal_incomplete (emptyWorld I)
      ((h (emptyWorld I) (conceal (emptyWorld I))
          (indisc_conceal (emptyWorld I))).mp (emptyWorld_complete I))

/-! ## The blindness -/

theorem not_know_complete (w : World I) : ¬ K w Complete :=
  fun h => conceal_incomplete w (h (conceal w) (indisc_conceal w))

/-- The failure is not a failure of the world to be complete.  A world with no
exterior at all is complete and still cannot know it. -/
theorem true_but_unknown (I : Type) :
    Complete (emptyWorld I) ∧ ¬ K (emptyWorld I) Complete :=
  ⟨emptyWorld_complete I, not_know_complete (emptyWorld I)⟩

/-- Appearance-omniscience does not help.  A system knowing every
appearance-determined truth still fails on `Complete`, because `Complete` is not
one of them. -/
theorem not_know_complete_appearance_omniscient (w : World I)
    (_KAll : ∀ P : World I → Prop, AppDetermined P → P w → K w P) :
    ¬ K w Complete :=
  not_know_complete w

/-! ## The asymmetry

Incompleteness is knowable when it holds.  Completeness never is.  This is the
counterpart of the `U` / `Upos` split in the aseity development, and it survives
the move to totality: a single appearance settles the existential, and no set of
appearances settles the universal denial. -/

theorem know_incomplete (w : World I) (i : I) (h : App w i) :
    K w (fun w' => ¬ Complete w') :=
  fun _ hw hc => match (hw i).mp h with | ⟨e, _⟩ => hc e

/-- Knowledge here is substantive, not vacuous: the system knows its own
appearances exactly. -/
theorem knows_own_appearances (w : World I) :
    K w (fun w' => ∀ i, App w' i ↔ App w i) :=
  fun _ hw i => (hw i).symm

/-! ## The price

Transparency would deliver completeness from an absence of appearances.  So the
argument turns entirely on whether a traceless exterior is possible.  Restrict
the space of worlds to transparent ones and the blindness lifts. -/

theorem transparent_no_appearance_complete (w : World I)
    (ht : Transparent w) (hn : ∀ i, ¬ App w i) : Complete w :=
  fun e => match ht e with | ⟨i, hi⟩ => hn i ⟨e, hi⟩

/-- Knowledge relativised to transparent worlds. -/
def KT (w : World I) (P : World I → Prop) : Prop :=
  ∀ w', Transparent w' → Indisc w w' → P w'

theorem KT_knows_complete (w : World I) (hn : ∀ i, ¬ App w i) : KT w Complete :=
  fun w' ht hw =>
    transparent_no_appearance_complete w' ht (fun i hi => hn i ((hw i).mpr hi))

/-! ## The regress

Transparency is not itself knowable, and by the same construction.  This is what
does the work a diagonal argument would otherwise do, and it terminates after one
step rather than repeating. -/

theorem not_know_transparent (w : World I) : ¬ K w Transparent :=
  fun h => conceal_not_transparent w (h (conceal w) (indisc_conceal w))

theorem know_complete_given_transparency (w : World I)
    (hn : ∀ i, ¬ App w i) (ht : K w Transparent) : K w Complete :=
  fun w' hw =>
    transparent_no_appearance_complete w' (ht w' hw)
      (fun i hi => hn i ((hw i).mpr hi))

/-- The dilemma, stated in one place: completeness is unknowable, and the premise
that would yield it is unknowable too. -/
theorem dilemma (w : World I) : ¬ K w Complete ∧ ¬ K w Transparent :=
  ⟨not_know_complete w, not_know_transparent w⟩


/-! ## The actual world

Two candidate premises, which come apart.

`ExtInhabited` is metaphysical: something lies outside.
`SomeAppearance` is epistemic: something outside shows up inside.

The second entails the first.  The first entails nothing epistemic at all. -/

def ExtInhabited (w : World I) : Prop := ∃ _ : w.Ext, True

def SomeAppearance (w : World I) : Prop := ∃ i, App w i

theorem appearance_gives_ext (w : World I) (h : SomeAppearance w) :
    ExtInhabited w :=
  match h with | ⟨_, ⟨e, _⟩⟩ => ⟨e, trivial⟩

theorem ext_inhabited_incomplete (w : World I) (h : ExtInhabited w) :
    ¬ Complete w :=
  match h with | ⟨e, _⟩ => fun hc => hc e

/-- A world with an exterior that never shows: the metaphysical premise holds,
the epistemic one fails. -/
def W_hidden (I : Type) : World I := conceal (emptyWorld I)

theorem hidden_ext_inhabited (I : Type) : ExtInhabited (W_hidden I) :=
  ⟨Sum.inr (), trivial⟩

theorem hidden_no_appearance (I : Type) : ¬ SomeAppearance (W_hidden I) :=
  fun h => match h with
    | ⟨_, ⟨Sum.inl e, _⟩⟩ => Empty.elim e
    | ⟨_, ⟨Sum.inr _, he⟩⟩ => he

/-- The metaphysical premise is epistemically inert.  A world can have an
exterior and be unable to know it has one. -/
theorem hidden_does_not_know_incomplete (I : Type) :
    ¬ K (W_hidden I) (fun w' => ¬ Complete w') :=
  fun h =>
    h (emptyWorld I) (indisc_symm (indisc_conceal (emptyWorld I)))
      (emptyWorld_complete I)

/-- A concrete actual world satisfying the epistemic premise. -/
def W_actual : World Unit := { Ext := Unit, trace := fun _ _ => True }

theorem actual_appearance : SomeAppearance W_actual := ⟨(), (), trivial⟩

theorem actual_ext_inhabited : ExtInhabited W_actual :=
  appearance_gives_ext W_actual actual_appearance

/-! ### What the actual world can and cannot know -/

section Actual
variable (W : World I)

theorem actual_knows_incomplete (h : SomeAppearance W) :
    K W (fun w' => ¬ Complete w') :=
  match h with | ⟨i, hi⟩ => know_incomplete W i hi

/-- The full verdict.  Given an appearance, the actual world knows it is not
complete, still cannot know it is complete, and cannot know its exterior is
exhausted by what appears. -/
theorem actual_verdict (h : SomeAppearance W) :
    K W (fun w' => ¬ Complete w')
      ∧ ¬ K W Complete
      ∧ ¬ K W Transparent :=
  ⟨actual_knows_incomplete W h, not_know_complete W, not_know_transparent W⟩

end Actual

/-- The separation, in one statement: the epistemic premise entails the
metaphysical one, and the converse fails. -/
theorem premises_not_equivalent (I : Type) :
    (∀ w : World I, SomeAppearance w → ExtInhabited w)
      ∧ (ExtInhabited (W_hidden I) ∧ ¬ SomeAppearance (W_hidden I)) :=
  ⟨fun w => appearance_gives_ext w,
   ⟨hidden_ext_inhabited I, hidden_no_appearance I⟩⟩


/-! ## Relevance

Objection: `K` quantifies over every indiscernible world, so failing it is
cheap.  Real knowledge tolerates ignoring far-fetched alternatives.

Answer: weaken `K` by an arbitrary relevance ordering `R`, so the knower may
discard alternatives it deems remote.  Two conditions on `R` are enough to make
the blindness survive, and neither mentions `conceal`:

  * reflexivity, which is what makes the weakened operator factive;
  * appearance-determination, which is what lets the knower apply the ordering
    from inside.

Together they force the weakened operator to coincide with `K` exactly.  So the
strictness of `K` is not an artefact.  Any relevance ordering a knower could
actually wield is the strict one. -/

def KR (R : World I → World I → Prop) (w : World I) (P : World I → Prop) : Prop :=
  ∀ w', R w w' → Indisc w w' → P w'

/-- Relevance is settled by how things appear.  Without this the knower cannot
tell which alternatives its own ordering discards. -/
def RelAppDet (R : World I → World I → Prop) : Prop :=
  ∀ w w' v, Indisc w w' → (R w v ↔ R w' v)

theorem K_gives_KR (R : World I → World I → Prop) (w : World I)
    (P : World I → Prop) (h : K w P) : KR R w P :=
  fun w' _ hi => h w' hi

theorem KR_factive (R : World I → World I → Prop) (hrefl : ∀ w, R w w)
    (w : World I) (P : World I → Prop) (h : KR R w P) : P w :=
  h w (hrefl w) (indisc_refl w)

/-- The collapse.  A reflexive, appearance-determined relevance ordering buys
no permissiveness whatever. -/
theorem relevance_collapse (R : World I → World I → Prop)
    (hrefl : ∀ w, R w w) (hdet : RelAppDet R) (w : World I) (P : World I → Prop) :
    KR R w P ↔ K w P :=
  ⟨fun h w' hi => h w' ((hdet w w' w' hi).mpr (hrefl w')) hi,
   fun h w' _ hi => h w' hi⟩

/-- Blindness survives permissiveness. -/
theorem not_KR_complete (R : World I → World I → Prop)
    (hrefl : ∀ w, R w w) (hdet : RelAppDet R) (w : World I) : ¬ KR R w Complete :=
  fun h =>
    conceal_incomplete w
      ((relevance_collapse R hrefl hdet w Complete).mp h (conceal w) (indisc_conceal w))

theorem not_KR_transparent (R : World I → World I → Prop)
    (hrefl : ∀ w, R w w) (hdet : RelAppDet R) (w : World I) : ¬ KR R w Transparent :=
  fun h =>
    conceal_not_transparent w
      ((relevance_collapse R hrefl hdet w Transparent).mp h (conceal w) (indisc_conceal w))

/-- Contrapositive: knowing completeness requires an ordering whose verdicts are
not fixed by appearances. -/
theorem knowing_complete_needs_hidden_relevance (R : World I → World I → Prop)
    (hrefl : ∀ w, R w w) (w : World I) (h : KR R w Complete) : ¬ RelAppDet R :=
  fun hdet => not_KR_complete R hrefl hdet w h

/-! ### The escape and its price

`Rid` is the maximally permissive ordering: only actuality is relevant.  Under it
every truth is known, including completeness.  It is not appearance-determined,
and the price is exact: its verdicts differ across worlds the knower cannot tell
apart, so the knower cannot certify that it holds. -/

def Rid : World I → World I → Prop := fun w v => v = w

theorem Rid_refl (w : World I) : Rid w w := rfl

theorem Rid_knows_every_truth (w : World I) (P : World I → Prop) (h : P w) :
    KR Rid w P :=
  fun _ he _ => he ▸ h

theorem empty_ne_hidden (I : Type) : emptyWorld I ≠ W_hidden I :=
  fun he => Empty.elim (cast (congrArg World.Ext he).symm (Sum.inr ()))

theorem Rid_not_appDet (I : Type) : ¬ RelAppDet (I := I) Rid :=
  fun hdet =>
    empty_ne_hidden I
      ((hdet (emptyWorld I) (W_hidden I) (emptyWorld I)
          (indisc_conceal (emptyWorld I))).mp rfl)

/-- The price, stated.  Two worlds the knower cannot distinguish, opposite
verdicts on whether completeness is known. -/
theorem verdict_invisible_to_knower (I : Type) :
    Indisc (emptyWorld I) (W_hidden I)
      ∧ KR Rid (emptyWorld I) Complete
      ∧ ¬ KR Rid (W_hidden I) Complete :=
  ⟨indisc_conceal (emptyWorld I),
   Rid_knows_every_truth (emptyWorld I) Complete (emptyWorld_complete I),
   fun h =>
     conceal_incomplete (emptyWorld I)
       (KR_factive Rid Rid_refl (W_hidden I) Complete h)⟩

/-! ## Branching

The modal instance.  `Ext` becomes the unrealised continuations of the present,
and `trace` becomes how a possibility shows up now: a power, a disposition, a
tendency.  `Complete` becomes the claim that the present exhausts reality, and
`Transparent` becomes the actualist thesis that every possibility is grounded in
some present power.

Nothing new is proved here.  The point is that the earlier theorems already are
the theorems about an open future, once the exterior is read modally. -/

structure Tense (I : Type) where
  Branch : Type
  mark   : Branch → I → Prop

def toWorld (t : Tense I) : World I := ⟨t.Branch, t.mark⟩

/-- The present exhausts reality: no unrealised continuation. -/
def Closed (t : Tense I) : Prop := Complete (toWorld t)

/-- Some possibility marks the present. -/
def Powers (t : Tense I) : Prop := SomeAppearance (toWorld t)

/-- Every possibility is grounded in a present power. -/
def Grounded (t : Tense I) : Prop := Transparent (toWorld t)

def KB (t : Tense I) (P : World I → Prop) : Prop := K (toWorld t) P

/-- No present state can know it is all there is. -/
theorem no_present_knows_closure (t : Tense I) : ¬ KB t Complete :=
  not_know_complete (toWorld t)

/-- Powers reveal openness.  A disposition registering now is enough to know the
present is not total. -/
theorem powers_reveal_openness (t : Tense I) (h : Powers t) :
    KB t (fun w => ¬ Complete w) :=
  actual_knows_incomplete (toWorld t) h

/-- The actualist grounding thesis cannot be known from within the present. -/
theorem cannot_know_powers_exhaust (t : Tense I) : ¬ KB t Transparent :=
  not_know_transparent (toWorld t)

/-- The verdict on the open future.  Given present powers: the present is known
not to exhaust reality, is never known to exhaust it, and the possibilities are
never known to be exhausted by the powers that mark them. -/
theorem branching_verdict (t : Tense I) (h : Powers t) :
    KB t (fun w => ¬ Complete w)
      ∧ ¬ KB t Complete
      ∧ ¬ KB t Transparent :=
  ⟨powers_reveal_openness t h, no_present_knows_closure t,
   cannot_know_powers_exhaust t⟩

/-- Time does not settle it.  The blindness holds at every stage of any
sequence of present states, so no amount of unfolding verifies closure. -/
theorem no_stage_settles_closure (s : Nat → Tense I) :
    ∀ n, ¬ KB (s n) Complete :=
  fun n => no_present_knows_closure (s n)

/-- And it survives permissive knowledge, by the collapse theorem. -/
theorem branching_verdict_relevant (R : World I → World I → Prop)
    (hrefl : ∀ w, R w w) (hdet : RelAppDet R) (t : Tense I) :
    ¬ KR R (toWorld t) Complete ∧ ¬ KR R (toWorld t) Transparent :=
  ⟨not_KR_complete R hrefl hdet (toWorld t),
   not_KR_transparent R hrefl hdet (toWorld t)⟩


/-! ## Reality as knower

Suppose reality itself is the system.  Then its exterior is empty by
stipulation, so `Complete` holds of it.  The question is whether it can know
that, and there are exactly three routes.  None breaks the theorem.  Together
they locate the disagreement precisely. -/

def W_reality (I : Type) : World I := emptyWorld I

theorem reality_complete (I : Type) : Complete (W_reality I) :=
  emptyWorld_complete I

/-- Route 1: reality knows by inspecting what appears.  Then it is complete and
cannot verify it.  Nothing in its appearances distinguishes it from a world with
a concealed exterior. -/
theorem reality_blind (I : Type) :
    Complete (W_reality I) ∧ ¬ K (W_reality I) Complete :=
  true_but_unknown I

/-- Route 2: restrict the alternatives to complete worlds, on the ground that
reality could not have had an exterior.  This ordering is appearance-determined
but not reflexive, and that is fatal. -/
def RComplete : World I → World I → Prop := fun _ v => Complete v

theorem RComplete_appDet : RelAppDet (I := I) RComplete :=
  fun _ _ _ _ => Iff.rfl

/-- The verdict is delivered at every world whatsoever, complete or not. -/
theorem RComplete_verdict (w : World I) : KR RComplete w Complete :=
  fun _ hc _ => hc

/-- So it is not knowledge.  An incomplete world receives the same verdict. -/
theorem RComplete_not_factive (I : Type) :
    KR RComplete (W_hidden I) Complete ∧ ¬ Complete (W_hidden I) :=
  ⟨RComplete_verdict (W_hidden I), conceal_incomplete (emptyWorld I)⟩

theorem RComplete_not_refl (I : Type) : ¬ (∀ w : World I, RComplete w w) :=
  fun h => conceal_incomplete (emptyWorld I) (h (W_hidden I))

/-- Route 3: constitutive knowledge, not grounded in appearances at all.  This
is consistent and factive and reality does know its own completeness.  The price
is `Rid_not_appDet` and `verdict_invisible_to_knower`: the knowing cannot be
certified from within, and an indiscernible world receives the opposite
verdict. -/
theorem reality_constitutive (I : Type) : KR Rid (W_reality I) Complete :=
  Rid_knows_every_truth (W_reality I) Complete (reality_complete I)

/-- The trilemma.  Inspection gives blindness; restriction gives a verdict that
tracks nothing; constitution gives knowledge that cannot be told from inside. -/
theorem reality_trilemma (I : Type) :
    (¬ K (W_reality I) Complete)
      ∧ (KR RComplete (W_hidden I) Complete ∧ ¬ Complete (W_hidden I))
      ∧ (KR Rid (W_reality I) Complete ∧ ¬ RelAppDet (I := I) Rid) :=
  ⟨(true_but_unknown I).2,
   RComplete_not_factive I,
   ⟨reality_constitutive I, Rid_not_appDet I⟩⟩

end Totality

#print axioms Totality.indisc_conceal
#print axioms Totality.complete_not_appDetermined
#print axioms Totality.not_know_complete
#print axioms Totality.true_but_unknown
#print axioms Totality.not_know_complete_appearance_omniscient
#print axioms Totality.know_incomplete
#print axioms Totality.knows_own_appearances
#print axioms Totality.KT_knows_complete
#print axioms Totality.not_know_transparent
#print axioms Totality.know_complete_given_transparency
#print axioms Totality.dilemma
#print axioms Totality.appearance_gives_ext
#print axioms Totality.hidden_no_appearance
#print axioms Totality.hidden_does_not_know_incomplete
#print axioms Totality.actual_appearance
#print axioms Totality.actual_knows_incomplete
#print axioms Totality.actual_verdict
#print axioms Totality.premises_not_equivalent
#print axioms Totality.relevance_collapse
#print axioms Totality.not_KR_complete
#print axioms Totality.not_KR_transparent
#print axioms Totality.knowing_complete_needs_hidden_relevance
#print axioms Totality.Rid_not_appDet
#print axioms Totality.verdict_invisible_to_knower
#print axioms Totality.no_present_knows_closure
#print axioms Totality.powers_reveal_openness
#print axioms Totality.cannot_know_powers_exhaust
#print axioms Totality.branching_verdict
#print axioms Totality.no_stage_settles_closure
#print axioms Totality.branching_verdict_relevant
#print axioms Totality.reality_blind
#print axioms Totality.RComplete_appDet
#print axioms Totality.RComplete_not_factive
#print axioms Totality.RComplete_not_refl
#print axioms Totality.reality_constitutive
#print axioms Totality.reality_trilemma
