-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceHasBranch_proof_10f9df4949f3
-- name    : P2M_GroundTheory_Heights__Heights_PlaceHasBranch_proof_10f9df4949f3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:34:36.040797+00:00
-- url     : https://prove2.me/theorems/4d909aa5-8fe7-462c-8b0b-85475e4cdcfc
-- title:
--   P2 M Ground Theory Heights  Heights Place Has Branch proof 10f9df4949f3: P2 M Ground Theory Heights  Heights Place Has Branch proof 10f9df4949f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Has Branch proof 10f9df4949f3 construction uses the P2 M Ground Theory Heights  Heights Place Has Branch proof 10f9df4949f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPlaceHasBranch.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPlaceHasBranch.lean#L12-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceHasBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceBranchExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchInOneBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPlaceHasBranch
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

theorem P2M_GroundTheory_Heights__Heights_PlaceHasBranch_proof_10f9df4949f3 (h₁ : PlaceBranchExists.Statement) (h₂ : PuncturedBranchInOneBranch.Statement)
    (h₃ : PuncturedBranchSameOrder.Statement) : PlaceHasBranch.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceHasBranch».«proof» := P2M_GroundTheory_Heights__Heights_PlaceHasBranch_proof_10f9df4949f3
