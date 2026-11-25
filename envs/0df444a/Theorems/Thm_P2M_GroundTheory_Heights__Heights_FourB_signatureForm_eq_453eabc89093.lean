-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_signatureForm_eq_453eabc89093
-- name    : P2M_GroundTheory_Heights__Heights_FourB_signatureForm_eq_453eabc89093
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:26.42413+00:00
-- url     : https://prove2.me/theorems/7c193255-7040-4dfb-aa18-f1b585cb7bb6
-- title:
--   P2 M Ground Theory Heights  Heights Four B signature Form eq 453eabc89093: P2 M Ground Theory Heights  Heights Four B signature Form eq 453eabc89093
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B signature Form eq 453eabc89093 construction uses the P2 M Ground Theory Heights  Heights Four B signature Form eq 453eabc89093 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L37-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
variable {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FourB_signatureForm_eq_453eabc89093 (p : ℕ) :
    signatureForm N p = diagonal fun a => ((sigSign p a : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«signatureForm_eq» := P2M_GroundTheory_Heights__Heights_FourB_signatureForm_eq_453eabc89093
