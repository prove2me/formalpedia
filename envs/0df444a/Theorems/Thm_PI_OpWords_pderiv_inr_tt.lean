-- Prove2me | Theorems.Thm_PI_OpWords_pderiv_inr_tt
-- name    : PI.OpWords.pderiv_inr_tt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:35.598184+00:00
-- url     : https://prove2.me/theorems/2a7b2533-54d7-4b0e-b817-02fbb57d687d
-- title:
--   Op Words: pderiv inr tt
-- statement:
--   The Op Words construction uses the pderiv inr tt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L16-L18

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

theorem PI.OpWords.pderiv_inr_tt (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    pderiv (Sum.inr a) (tt K k) = X (Sum.inl a) := by sorry
