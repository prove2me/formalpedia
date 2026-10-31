-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_passive_and_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.passive_and_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:18:38.849168+00:00
-- url     : https://prove2.me/theorems/5d7287e9-218b-4501-8acb-5131ba67698b
-- title:
--   Passive secure AND from password identification
-- statement:
--   Let an identification execution have correctness error at most $\delta\ge0$ and passive statistical privacy error at most $\varepsilon\ge0$. A local view includes the publicly announced accept/reject decision. Privacy means that at a fixed local password, the views for any two different, unequal other passwords have trace distance at most $\varepsilon$. Choose three distinct passwords $w_0,w'_0,w_1$. Alice encodes input $a$ by $w_0$ or $w_1$; Bob encodes $b$ by $w'_0$ or $w_1$, respectively. Both output the identification decision $D$. Then
--
--   $$\Pr[D=a\land b]\ge1-\delta.$$
--
--   The two players have the same output law. For Alice, any two input pairs with the same $a$ and the same ideal AND output have local views at trace distance at most $\varepsilon$; the corresponding statement holds for Bob at fixed $b$. Thus the executed reduction preserves passive correctness and statistical privacy. The input maps are prescribed; this statement makes no claim about malicious deviations.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 3, §1, unnumbered: passive-secure AND reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)

open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Positive list length and inhabited fibers supply the tagged union's inhabitant.
This derived instance adds no hypothesis to Lemma 2.2. -/
local instance {m : ℕ} [NeZero m] {A : Fin m → Type*}
    [∀ i, Nonempty (A i)] : Nonempty (Sigma A) :=
  ⟨⟨0, Classical.choice (inferInstance : Nonempty (A 0))⟩⟩

/-- PDF p.3, unnumbered passive AND reduction. Both parties receive the
identification decision. Correctness and full-view privacy are preserved for
the prescribed maps; no malicious-security claim is made. -/
theorem passive_and_reduction
    {W EA EB : Type*} [Fintype EA] [Fintype EB]
    (P : PassiveExecution W EA EB) (wzero wzeroOther wone : W)
    (hzero : wzero ≠ wzeroOther) (hleft : wzero ≠ wone)
    (hright : wzeroOther ≠ wone) (delta epsilon : ℝ)
    (hsecurity : PassiveEqualitySecurity P delta epsilon) :
    (∀ a b : Bool,
      blockMass (P.bob (andPassword wzero wone a)
        (andPassword wzeroOther wone b)) (a && b) ≥ 1 - delta ∧
      ∀ t, blockMass (P.alice (andPassword wzero wone a)
        (andPassword wzeroOther wone b)) t =
        blockMass (P.bob (andPassword wzero wone a)
          (andPassword wzeroOther wone b)) t) ∧
    (∀ a b c : Bool, (a && b) = (a && c) →
      cqDistance (P.alice (andPassword wzero wone a) (andPassword wzeroOther wone b))
        (P.alice (andPassword wzero wone a) (andPassword wzeroOther wone c)) ≤ epsilon) ∧
    (∀ b a c : Bool, (a && b) = (c && b) →
      cqDistance (P.bob (andPassword wzero wone a) (andPassword wzeroOther wone b))
        (P.bob (andPassword wzero wone c) (andPassword wzeroOther wone b)) ≤ epsilon) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
