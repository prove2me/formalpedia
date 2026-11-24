-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_final_alg
-- name    : PI.PolynomialProperness.CoreW.final_alg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:54.442846+00:00
-- url     : https://prove2.me/theorems/895b654d-14a6-443a-8fb8-807f564520e1
-- title:
--   Core W: final alg
-- statement:
--   The Core W construction uses the final alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L114-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/IsoRightInv.lean#L114-L127

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.PolynomialProperness.CoreW.final_alg (D R0 E K c X a b : ℝ) (hD0 : 0 ≤ D) (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hc : c = 1 + D * K) (ha : a ≤ D ^ 2 * R0 ^ 2 * K * X) (hb : b ≤ c * (E ^ 2 * X)) :
    2 * a + 2 * b ≤ (2 * D ^ 2 * R0 ^ 2 + 2 * (1 + D) * E ^ 2) * (1 + K) ^ 2 * X := by sorry
