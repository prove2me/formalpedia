-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimePlaceBranchExists_proof_265938788939
-- name    : P2M_GroundTheory_Heights__Heights_PrimePlaceBranchExists_proof_265938788939
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:01.82462+00:00
-- url     : https://prove2.me/theorems/f399ccd1-f2b5-5a4b-8f07-2f7f225cb236
-- title:
--   P2 M Ground Theory Heights  Heights Prime Place Branch Exists proof 265938788939: P2 M Ground Theory Heights  Heights Prime Place Branch Exists proof 265938788939
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Place Branch Exists proof 265938788939 construction uses the P2 M Ground Theory Heights  Heights Prime Place Branch Exists proof 265938788939 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimePlaceBranchExists.lean#L14-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimePlaceBranchExists.lean#L14-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimePlaceBranchExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPointOfPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProjectionLocallyInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimePlaceBranchExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelExists_proof_269d895ff472
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalDimDomain_proof_aafc8deef599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MaximalIdealHeightFG_proof_60a444887d99

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

theorem P2M_GroundTheory_Heights__Heights_PrimePlaceBranchExists_proof_265938788939 (hA : NormalModelPointOfPlace.Statement) (hB : NormalModelDisc.Statement)
    (hC : NormalModelProjectionLocallyInjective.Statement) (hO : NormalCurveBranchOrder.Statement) :
    PrimePlaceBranchExists.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimePlaceBranchExists».«proof» := P2M_GroundTheory_Heights__Heights_PrimePlaceBranchExists_proof_265938788939
