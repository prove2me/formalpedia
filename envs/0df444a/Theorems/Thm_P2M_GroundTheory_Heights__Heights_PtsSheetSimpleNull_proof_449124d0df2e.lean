-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_proof_449124d0df2e
-- name    : P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_proof_449124d0df2e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:18.185401+00:00
-- url     : https://prove2.me/theorems/bb87b3cb-41be-4689-9302-4afbaca49a19
-- title:
--   P2 M Ground Theory Heights  Heights Pts Sheet Simple Null proof 449124d0df2e: P2 M Ground Theory Heights  Heights Pts Sheet Simple Null proof 449124d0df2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Sheet Simple Null proof 449124d0df2e construction uses the P2 M Ground Theory Heights  Heights Pts Sheet Simple Null proof 449124d0df2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetSimpleNull.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetSimpleNull.lean#L55-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetSimpleNull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_proof_449124d0df2e (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsSheetSimpleNull».«proof» := P2M_GroundTheory_Heights__Heights_PtsSheetSimpleNull_proof_449124d0df2e
