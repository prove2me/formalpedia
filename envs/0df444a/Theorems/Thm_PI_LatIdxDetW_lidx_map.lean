-- Prove2me | Theorems.Thm_PI_LatIdxDetW_lidx_map
-- name    : PI.LatIdxDetW.lidx_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:01.596332+00:00
-- url     : https://prove2.me/theorems/6a54828f-491e-52f7-a982-38caabd040db
-- title:
--   Lat Idx Det W: lidx map
-- statement:
--   The Lat Idx Det W construction uses the lidx map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L82-L85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

theorem PI.LatIdxDetW.lidx_map (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (A B : Submodule R W) :
    lidx p (A.map (φ : W →ₗ[R] W')) (B.map (φ : W →ₗ[R] W')) = lidx p A B := by sorry
