-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongPolyLimit_proof_e5a6fc45a49a
-- name    : P2M_GroundTheory_Heights__Heights_Targets_LelongPolyLimit_proof_e5a6fc45a49a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:36.815263+00:00
-- url     : https://prove2.me/theorems/d47aa3be-0ac8-454c-8693-7f583cfdbeab
-- title:
--   P2 M Ground Theory Heights  Heights Targets Lelong Poly Limit proof e5a6fc45a49a: P2 M Ground Theory Heights  Heights Targets Lelong Poly Limit proof e5a6fc45a49a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Lelong Poly Limit proof e5a6fc45a49a construction uses the P2 M Ground Theory Heights  Heights Targets Lelong Poly Limit proof e5a6fc45a49a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongPolyLimit.lean#L30-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongPolyLimit.lean#L30-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongPolyLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongPolyLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b

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
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

theorem P2M_GroundTheory_Heights__Heights_Targets_LelongPolyLimit_proof_e5a6fc45a49a (hGraph : VarIntGraph.Statement) (hMult : LocalMultComap.Statement)
    (hWeight : LelongWeightLimit.Statement) : LelongPolyLimit.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«LelongPolyLimit».«proof» := P2M_GroundTheory_Heights__Heights_Targets_LelongPolyLimit_proof_e5a6fc45a49a
