-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GeoNumTarget_isFieldIntersection_intNum_3925b23cf106
-- name    : P2M_GroundTheory_Heights__Heights_GeoNumTarget_isFieldIntersection_intNum_3925b23cf106
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:54.886891+00:00
-- url     : https://prove2.me/theorems/cc10fdef-765f-528a-a438-7702b5ced541
-- title:
--   P2 M Ground Theory Heights  Heights Geo Num Target is Field Intersection int Num 3925b23cf106: P2 M Ground Theory Heights  Heights Geo Num Target is Field Intersection int Num 3925b23cf106
-- statement:
--   The P2 M Ground Theory Heights  Heights Geo Num Target is Field Intersection int Num 3925b23cf106 construction uses the P2 M Ground Theory Heights  Heights Geo Num Target is Field Intersection int Num 3925b23cf106 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L67-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GeoNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
open GroundTheory.Heights₂.Heights.GeoNumTarget
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GeoNumTarget_isFieldIntersection_intNum_3925b23cf106 (p : ℕ) [Fact p.Prime] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := ZMod p) (ι := ι)
      (fun V _ L => NumbersDVR.intNum (ZMod p) V L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GeoNumTarget».«isFieldIntersection_intNum» := P2M_GroundTheory_Heights__Heights_GeoNumTarget_isFieldIntersection_intNum_3925b23cf106
