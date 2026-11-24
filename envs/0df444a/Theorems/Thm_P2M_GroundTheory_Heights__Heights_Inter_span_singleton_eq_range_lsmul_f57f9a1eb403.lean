-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_span_singleton_eq_range_lsmul_f57f9a1eb403
-- name    : P2M_GroundTheory_Heights__Heights_Inter_span_singleton_eq_range_lsmul_f57f9a1eb403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:22.398982+00:00
-- url     : https://prove2.me/theorems/7b2c55f1-b364-43ec-9c2f-fe52b4061c42
-- title:
--   P2 M Ground Theory Heights  Heights Inter span singleton eq range lsmul f57f9a1eb403: P2 M Ground Theory Heights  Heights Inter span singleton eq range lsmul f57f9a1eb403
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter span singleton eq range lsmul f57f9a1eb403 construction uses the P2 M Ground Theory Heights  Heights Inter span singleton eq range lsmul f57f9a1eb403 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/SpanSingletonEqRangeLsmul.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/SpanSingletonEqRangeLsmul.lean#L20-L23

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

theorem P2M_GroundTheory_Heights__Heights_Inter_span_singleton_eq_range_lsmul_f57f9a1eb403 {A : Type*} [CommRing A] (x : A) :
    Ideal.span {x} = LinearMap.range (LinearMap.lsmul A A x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«span_singleton_eq_range_lsmul» := P2M_GroundTheory_Heights__Heights_Inter_span_singleton_eq_range_lsmul_f57f9a1eb403
