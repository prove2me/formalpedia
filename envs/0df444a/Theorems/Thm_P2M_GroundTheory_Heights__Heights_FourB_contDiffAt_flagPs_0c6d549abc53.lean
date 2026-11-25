-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagPs_0c6d549abc53
-- name    : P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagPs_0c6d549abc53
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:39:56.381089+00:00
-- url     : https://prove2.me/theorems/218d898a-3d3b-5389-a9fb-5854a1aad9b4
-- title:
--   P2 M Ground Theory Heights  Heights Four B cont Diff At flag Ps 0c6d549abc53: P2 M Ground Theory Heights  Heights Four B cont Diff At flag Ps 0c6d549abc53
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B cont Diff At flag Ps 0c6d549abc53 construction uses the P2 M Ground Theory Heights  Heights Four B cont Diff At flag Ps 0c6d549abc53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L122-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L122-L155

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

theorem P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagPs_0c6d549abc53 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → (LowerPair N → ℂ)} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0) :
    ContDiffAt ℝ 2 (fun z => flagPs N p i hi (g z)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«contDiffAt_flagPs» := P2M_GroundTheory_Heights__Heights_FourB_contDiffAt_flagPs_0c6d549abc53
