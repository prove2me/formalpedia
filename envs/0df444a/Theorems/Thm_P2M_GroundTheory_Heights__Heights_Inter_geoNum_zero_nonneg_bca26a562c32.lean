-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_geoNum_zero_nonneg_bca26a562c32
-- name    : P2M_GroundTheory_Heights__Heights_Inter_geoNum_zero_nonneg_bca26a562c32
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:08.380823+00:00
-- url     : https://prove2.me/theorems/87f44e88-4703-475c-b628-9b2e2c9f7394
-- title:
--   P2 M Ground Theory Heights  Heights Inter geo Num zero nonneg bca26a562c32: P2 M Ground Theory Heights  Heights Inter geo Num zero nonneg bca26a562c32
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter geo Num zero nonneg bca26a562c32 construction uses the P2 M Ground Theory Heights  Heights Inter geo Num zero nonneg bca26a562c32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/SpanSingletonEqRangeLsmul.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/SpanSingletonEqRangeLsmul.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SpanSingletonEqRangeLsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_geoNum_zero_nonneg_bca26a562c32 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (b : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«geoNum_zero_nonneg» := P2M_GroundTheory_Heights__Heights_Inter_geoNum_zero_nonneg_bca26a562c32
