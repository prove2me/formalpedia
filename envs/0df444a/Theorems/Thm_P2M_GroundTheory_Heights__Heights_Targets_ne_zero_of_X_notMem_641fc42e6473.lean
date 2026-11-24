-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ne_zero_of_X_notMem_641fc42e6473
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ne_zero_of_X_notMem_641fc42e6473
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:41.704495+00:00
-- url     : https://prove2.me/theorems/b300fb87-0a2c-4c2a-8057-69884eec6a74
-- title:
--   P2 M Ground Theory Heights  Heights Targets ne zero of X not Mem 641fc42e6473: P2 M Ground Theory Heights  Heights Targets ne zero of X not Mem 641fc42e6473
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets ne zero of X not Mem 641fc42e6473 construction uses the P2 M Ground Theory Heights  Heights Targets ne zero of X not Mem 641fc42e6473 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/CurveCountObjects.lean#L76-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ne_zero_of_X_notMem_641fc42e6473 {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ne_zero_of_X_notMem» := P2M_GroundTheory_Heights__Heights_Targets_ne_zero_of_X_notMem_641fc42e6473
