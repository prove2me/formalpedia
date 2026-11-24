-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_log_regLine_0e45a6823993
-- name    : P2M_GroundTheory_Heights__Heights_Targets_log_regLine_0e45a6823993
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:38.210341+00:00
-- url     : https://prove2.me/theorems/da7553a0-22f4-4796-8490-5a148c548c77
-- title:
--   P2 M Ground Theory Heights  Heights Targets log reg Line 0e45a6823993: P2 M Ground Theory Heights  Heights Targets log reg Line 0e45a6823993
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets log reg Line 0e45a6823993 construction uses the P2 M Ground Theory Heights  Heights Targets log reg Line 0e45a6823993 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L46-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_log_regLine_0e45a6823993 (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : (fun z => Real.log ((regLine A s ε ha hs).h z)) = regLog A s ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«log_regLine» := P2M_GroundTheory_Heights__Heights_Targets_log_regLine_0e45a6823993
