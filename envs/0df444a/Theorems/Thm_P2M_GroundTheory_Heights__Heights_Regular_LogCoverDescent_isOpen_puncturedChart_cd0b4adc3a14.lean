-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_isOpen_puncturedChart_cd0b4adc3a14
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_isOpen_puncturedChart_cd0b4adc3a14
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:43.969163+00:00
-- url     : https://prove2.me/theorems/0b65d814-3af5-4352-8df9-f858cb153f93
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent is Open punctured Chart cd0b4adc3a14: P2 M Ground Theory Heights  Heights Regular Log Cover Descent is Open punctured Chart cd0b4adc3a14
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent is Open punctured Chart cd0b4adc3a14 construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent is Open punctured Chart cd0b4adc3a14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L146-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_isOpen_puncturedChart_cd0b4adc3a14 : IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«isOpen_puncturedChart» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_isOpen_puncturedChart_cd0b4adc3a14
