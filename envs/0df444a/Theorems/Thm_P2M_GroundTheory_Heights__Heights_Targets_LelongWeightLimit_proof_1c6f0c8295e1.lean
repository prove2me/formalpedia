-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_proof_1c6f0c8295e1
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_proof_1c6f0c8295e1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:51.091342+00:00
-- url     : https://prove2.me/theorems/61710948-6956-4f76-b86a-4082269244d4
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit proof 1c6f0c8295e1: P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit proof 1c6f0c8295e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit proof 1c6f0c8295e1 construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Weight Limit proof 1c6f0c8295e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L70-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongWeightLimit.lean#L70-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_proof_e9b099c76968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3

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
open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)
open LelongWeightLimit

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_proof_1c6f0c8295e1 (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement)
    (hS : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement) (hD : LelongWeightDiff.Statement) :
    LelongWeightLimit.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongWeightLimit».«proof» := P2M_GroundTheory_Heights__Heights_Targets_LelongWeightLimit_proof_1c6f0c8295e1
