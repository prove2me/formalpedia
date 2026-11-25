-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_realForm_db376f7ec4df
-- name    : P2M_GroundTheory_Heights__Heights_det_realForm_db376f7ec4df
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:49.219255+00:00
-- url     : https://prove2.me/theorems/08ef4869-fbd6-4547-9955-29375ec8a38a
-- title:
--   P2 M Ground Theory Heights  Heights det real Form db376f7ec4df: P2 M Ground Theory Heights  Heights det real Form db376f7ec4df
-- statement:
--   The P2 M Ground Theory Heights  Heights det real Form db376f7ec4df construction uses the P2 M Ground Theory Heights  Heights det real Form db376f7ec4df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PComplexJacobian.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PComplexJacobian.lean#L36-L48

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

theorem P2M_GroundTheory_Heights__Heights_det_realForm_db376f7ec4df {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) :
    (realForm A).det = Complex.normSq A.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_realForm» := P2M_GroundTheory_Heights__Heights_det_realForm_db376f7ec4df
