-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_lincomb_bound
-- name    : PI.PolynomialProperness.CoreW.lincomb_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:33.378071+00:00
-- url     : https://prove2.me/theorems/2361d69a-d88b-4ca8-9fac-2550c44de081
-- title:
--   Core W: lincomb bound
-- statement:
--   The Core W construction uses the lincomb bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L147-L156

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
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
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.PolynomialProperness.CoreW.lincomb_bound (c : ι → ℂ) (q : ι → Fin n → ℂ) (a R : ℝ) (_hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ a) (hq : ∀ i, eN (q i) ≤ R) :
    eN (∑ i, c i • q i) ≤ (Fintype.card ι : ℝ) * a * R := by sorry
