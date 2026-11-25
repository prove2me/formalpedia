-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneTangent_eq_bot_6b94c19276ec
-- name    : P2M_GroundTheory_Heights__Heights_coneTangent_eq_bot_6b94c19276ec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:44.426445+00:00
-- url     : https://prove2.me/theorems/066eae3d-82ae-4f58-ba17-59dbac810b0d
-- title:
--   P2 M Ground Theory Heights  Heights cone Tangent eq bot 6b94c19276ec: P2 M Ground Theory Heights  Heights cone Tangent eq bot 6b94c19276ec
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Tangent eq bot 6b94c19276ec construction uses the P2 M Ground Theory Heights  Heights cone Tangent eq bot 6b94c19276ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L65-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
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
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_coneTangent_eq_bot_6b94c19276ec (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∉ coneSet h J) : coneTangent h J y = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneTangent_eq_bot» := P2M_GroundTheory_Heights__Heights_coneTangent_eq_bot_6b94c19276ec
