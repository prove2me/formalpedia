-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeBranchPlace_proof_1bf4c07d3526
-- name    : P2M_GroundTheory_Heights__Heights_PrimeBranchPlace_proof_1bf4c07d3526
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:16.863481+00:00
-- url     : https://prove2.me/theorems/81c62449-f9a2-44cd-b2ac-6d724f2df1c5
-- title:
--   P2 M Ground Theory Heights  Heights Prime Branch Place proof 1bf4c07d3526: P2 M Ground Theory Heights  Heights Prime Branch Place proof 1bf4c07d3526
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Branch Place proof 1bf4c07d3526 construction uses the P2 M Ground Theory Heights  Heights Prime Branch Place proof 1bf4c07d3526 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeBranchPlace.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeBranchPlace.lean#L14-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeBranchPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelExists_proof_269d895ff472

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
open MvPolynomial ComplexSets Filter Topology

theorem P2M_GroundTheory_Heights__Heights_PrimeBranchPlace_proof_1bf4c07d3526 (hD : PrimeBranchDimOne.Statement) (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement)
    (hA : NormalModelPlace.Statement) (hO : NormalCurveBranchOrder.Statement) : PrimeBranchPlace.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimeBranchPlace».«proof» := P2M_GroundTheory_Heights__Heights_PrimeBranchPlace_proof_1bf4c07d3526
