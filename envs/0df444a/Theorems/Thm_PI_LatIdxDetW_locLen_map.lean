-- Prove2me | Theorems.Thm_PI_LatIdxDetW_locLen_map
-- name    : PI.LatIdxDetW.locLen_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:13.738917+00:00
-- url     : https://prove2.me/theorems/737b5f03-973d-47b4-90f5-b53be6db00cc
-- title:
--   Lat Idx Det W: loc Len map
-- statement:
--   The Lat Idx Det W construction uses the loc Len map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L77-L80

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

theorem PI.LatIdxDetW.locLen_map (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (X Y : Submodule R W) :
    locLen p (X.map (φ : W →ₗ[R] W')) (Y.map (φ : W →ₗ[R] W')) = locLen p X Y := by sorry
