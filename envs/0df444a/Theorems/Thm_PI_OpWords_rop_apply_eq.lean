-- Prove2me | Theorems.Thm_PI_OpWords_rop_apply_eq
-- name    : PI.OpWords.rop_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:47.077922+00:00
-- url     : https://prove2.me/theorems/52d63e23-e73d-4408-b512-398ef6bf8174
-- title:
--   Op Words: rop apply eq
-- statement:
--   The Op Words construction uses the rop apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PolarizationBihomogeneous.lean#L9-L10

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

theorem PI.OpWords.rop_apply_eq (K : Type) [Field K] (k : ℕ) (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := by sorry
