-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneTangent_self_8b2ec418ba5d
-- name    : P2M_GroundTheory_Heights__Heights_mem_coneTangent_self_8b2ec418ba5d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:55.946555+00:00
-- url     : https://prove2.me/theorems/8c7811a8-1c05-4d57-95c7-828af5f56102
-- title:
--   P2 M Ground Theory Heights  Heights mem cone Tangent self 8b2ec418ba5d: P2 M Ground Theory Heights  Heights mem cone Tangent self 8b2ec418ba5d
-- statement:
--   The P2 M Ground Theory Heights  Heights mem cone Tangent self 8b2ec418ba5d construction uses the P2 M Ground Theory Heights  Heights mem cone Tangent self 8b2ec418ba5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L17-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_mem_coneTangent_self_8b2ec418ba5d {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    y ∈ coneTangent h J y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_coneTangent_self» := P2M_GroundTheory_Heights__Heights_mem_coneTangent_self_8b2ec418ba5d
