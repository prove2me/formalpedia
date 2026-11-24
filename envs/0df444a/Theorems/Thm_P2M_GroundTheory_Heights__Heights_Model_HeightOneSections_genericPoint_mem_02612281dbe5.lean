-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_genericPoint_mem_02612281dbe5
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_genericPoint_mem_02612281dbe5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:25.892071+00:00
-- url     : https://prove2.me/theorems/59d8cceb-794f-4398-bd70-9704758f680c
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections generic Point mem 02612281dbe5: P2 M Ground Theory Heights  Heights Model Height One Sections generic Point mem 02612281dbe5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections generic Point mem 02612281dbe5 construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections generic Point mem 02612281dbe5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L16-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_genericPoint_mem_02612281dbe5 {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«genericPoint_mem» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_genericPoint_mem_02612281dbe5
