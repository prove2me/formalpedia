-- Prove2me | Theorems.Thm_PI_OpWords_comp_mul_zero
-- name    : PI.OpWords.comp_mul_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:56.23594+00:00
-- url     : https://prove2.me/theorems/7d6b869e-6e0e-5fc5-bda1-8a64c4a28912
-- title:
--   Op Words: comp mul zero
-- statement:
--   The Op Words construction uses the comp mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L112-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L112-L138

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords

theorem PI.OpWords.comp_mul_zero {σ : Type} {K : Type} [Field K] (w : σ → ℤ) {φ : MvPolynomial σ K}
    (hφ : IsWeightedHomogeneous w φ 0) (n : ℤ) (ψ : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (φ * ψ) = φ * weightedHomogeneousComponent w n ψ := by sorry
