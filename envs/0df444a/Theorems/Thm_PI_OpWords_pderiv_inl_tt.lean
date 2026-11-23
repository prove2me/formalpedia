-- Prove2me | Theorems.Thm_PI_OpWords_pderiv_inl_tt
-- name    : PI.OpWords.pderiv_inl_tt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:34.123668+00:00
-- url     : https://prove2.me/theorems/c3c71e40-c484-43df-bb22-9408478e278e
-- title:
--   Op Words: pderiv inl tt
-- statement:
--   The Op Words construction uses the pderiv inl tt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L12-L14

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

theorem PI.OpWords.pderiv_inl_tt (K : Type) [Field K] (k : ℕ) (b : Fin k) :
    pderiv (Sum.inl b) (tt K k) = X (Sum.inr b) := by sorry
