-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_apply_eval_397ad03046bd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_apply_eval_397ad03046bd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:53.703517+00:00
-- url     : https://prove2.me/theorems/9df41237-7d1d-41b1-b968-252af805ca8d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers weight apply eval 397ad03046bd: P2 M Ground Theory Heights  Heights Field Numbers weight apply eval 397ad03046bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers weight apply eval 397ad03046bd construction uses the P2 M Ground Theory Heights  Heights Field Numbers weight apply eval 397ad03046bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L35-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_apply_eval_397ad03046bd {σ : Type*} (w : σ → K' → ℕ) (d : σ →₀ ℕ) (k' : K') :
    Finsupp.weight w d k' = Finsupp.weight (fun v => w v k') d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«weight_apply_eval» := P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_apply_eval_397ad03046bd
