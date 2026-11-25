-- Prove2me | Theorems.Thm_P2M_PI_LatIdxDetW_localization_map__381d41331f98
-- name    : P2M_PI_LatIdxDetW_localization_map__381d41331f98
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:26.432527+00:00
-- url     : https://prove2.me/theorems/5104d974-bc1b-531b-9682-422f1a296b35
-- title:
--   P2 M PI Lat Idx Det W localization map  381d41331f98: P2 M PI Lat Idx Det W localization map  381d41331f98
-- statement:
--   The P2 M PI Lat Idx Det W localization map  381d41331f98 construction uses the P2 M PI Lat Idx Det W localization map  381d41331f98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndexDeterminant/NegLogValuation.lean#L51-L54

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

theorem P2M_PI_LatIdxDetW_localization_map__381d41331f98 (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (L : Submodule R W) :
    localization₂ p (L.map (φ : W →ₗ[R] W')) = (localization₂ p L).map (φ : W →ₗ[R] W') := by sorry

alias «PI».«LatIdxDetW».«localization_map₂» := P2M_PI_LatIdxDetW_localization_map__381d41331f98
