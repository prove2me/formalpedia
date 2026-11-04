-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredFinishCall_lookup_word
-- name    : ThreeSum.WeightedGlobalColoredFinishCall.lookup_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:45:46.81302+00:00
-- url     : https://prove2.me/theorems/b09cc66e-74ec-4f50-b972-7a0afdd1abc6
-- title:
--   Weighted Global Colored Finish Call: lookup word
-- statement:
--   The Weighted Global Colored Finish Call construction uses the lookup word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinishCall.lean#L28-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredFinishCall.lean#L28-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredConcreteFinalCall
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLookupDepth
import Definitions.Def_Submission_Weighted_Global_TernaryColoredFinishCall
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredFinishCall
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup WeightedGlobalArenaLayout
open WeightedGlobalLocalParameters WeightedGlobalArenaSourceSetup WeightedGlobalColoredTerminalReceipt
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredFinishCall.lookup_word {lim : Limits} {d : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hcutoff : P.cutoff≤n)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free d) :
    ((fixedLength P.m+2*fixedLength P.m*(rounds P n)+16:ℕ):ℤ)≤lim.word := by sorry
