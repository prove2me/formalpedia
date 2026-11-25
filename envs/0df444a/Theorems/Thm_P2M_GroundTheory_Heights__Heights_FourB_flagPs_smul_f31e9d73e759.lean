-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_flagPs_smul_f31e9d73e759
-- name    : P2M_GroundTheory_Heights__Heights_FourB_flagPs_smul_f31e9d73e759
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:49.7896+00:00
-- url     : https://prove2.me/theorems/60cbb397-968c-4dc4-9ddd-30f20619e81e
-- title:
--   P2 M Ground Theory Heights  Heights Four B flag Ps smul f31e9d73e759: P2 M Ground Theory Heights  Heights Four B flag Ps smul f31e9d73e759
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B flag Ps smul f31e9d73e759 construction uses the P2 M Ground Theory Heights  Heights Four B flag Ps smul f31e9d73e759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L111-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
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
variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)

theorem P2M_GroundTheory_Heights__Heights_FourB_flagPs_smul_f31e9d73e759 (u : LowerPair N → ℂ) (t : ℝ) :
    flagPs N p i hi (t • u) =
      Real.log ‖((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«flagPs_smul» := P2M_GroundTheory_Heights__Heights_FourB_flagPs_smul_f31e9d73e759
