-- Prove2me | Theorems.Thm_PI_OpWords_coeff_X_pderiv_self
-- name    : PI.OpWords.coeff_X_pderiv_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:22.309791+00:00
-- url     : https://prove2.me/theorems/5535e0fe-d01f-5272-86e3-31491e58b916
-- title:
--   Op Words: coeff X pderiv self
-- statement:
--   The Op Words construction uses the coeff X pderiv self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L63-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L63-L83

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

theorem PI.OpWords.coeff_X_pderiv_self {σ : Type} {K : Type} [Field K] (i : σ) (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : coeff m (X i * pderiv i f) = coeff m f * (m i : K) := by sorry
