-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_realForm_mul_ef70b63d0cd1
-- name    : P2M_GroundTheory_Heights__Heights_realForm_mul_ef70b63d0cd1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:36.425217+00:00
-- url     : https://prove2.me/theorems/88757a0e-8e7d-5323-a2b9-ce2d2d113260
-- title:
--   P2 M Ground Theory Heights  Heights real Form mul ef70b63d0cd1: P2 M Ground Theory Heights  Heights real Form mul ef70b63d0cd1
-- statement:
--   The P2 M Ground Theory Heights  Heights real Form mul ef70b63d0cd1 construction uses the P2 M Ground Theory Heights  Heights real Form mul ef70b63d0cd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PComplexJacobian.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PComplexJacobian.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PComplexJacobian
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
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_realForm_mul_ef70b63d0cd1 {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ) :
    realForm (A * B) = realForm A * realForm B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«realForm_mul» := P2M_GroundTheory_Heights__Heights_realForm_mul_ef70b63d0cd1
