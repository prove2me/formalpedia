-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectorAllocation_word_envelope
-- name    : ThreeSum.WeightedGlobalArenaSelectorAllocation.word_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:21:27.18134+00:00
-- url     : https://prove2.me/theorems/76d0ae1d-54da-4cf0-b06f-28c577dbdff1
-- title:
--   Weighted Global Arena Selector Allocation: word envelope
-- statement:
--   The arena's fourth-power envelope pays the selector's genuine integer
--   cross products without replacing the score cap by the allocation size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L19-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L19-L32

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSelectorAllocation.word_envelope {T n score dB dC dP tB tC tP : ℕ}
    (hT : 1≤T) (hn : n≤T) (hs : score≤T)
    (hdB : dB≤T) (hdC : dC≤T) (hdP : dP≤T)
    (htB : tB≤T) (htC : tC≤T) (htP : tP≤T) :
    LightTernaryRowSelector.word n score dB dC dP tB tC tP≤(T+1)^4 := by sorry
