-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannelStep_callArgs_spec
-- name    : ThreeSum.LightTernaryMomentChannelStep.callArgs_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:46.892391+00:00
-- url     : https://prove2.me/theorems/c4994329-c84f-4bf9-be90-376cfd2339ce
-- title:
--   Light Ternary Moment Channel Step: call Args spec
-- statement:
--   The Light Ternary Moment Channel Step construction uses the call Args spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean#L15-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannelStep.lean#L15-L25

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000

theorem ThreeSum.LightTernaryMomentChannelStep.callArgs_spec {lim : Limits} {loc μ : ℕ→ℤ} (positions : List ℕ) (vals : List ℤ)
    (hloc : ∀ i∈positions, loc i=frame vals i)
    (hword : ∀ i∈positions, |frame vals i|≤lim.word) :
    (∀ e∈callArgs positions, e.Safe lim ⟨loc,μ⟩) ∧
      (callArgs positions).map (·.val ⟨loc,μ⟩)=values positions vals := by sorry
