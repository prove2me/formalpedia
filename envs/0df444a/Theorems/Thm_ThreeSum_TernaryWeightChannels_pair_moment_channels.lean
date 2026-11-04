-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightChannels_pair_moment_channels
-- name    : ThreeSum.TernaryWeightChannels.pair_moment_channels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:53.230708+00:00
-- url     : https://prove2.me/theorems/013d9c0b-34fb-4fdc-9d1d-87fbcad38421
-- title:
--   Ternary Weight Channels: pair moment channels
-- statement:
--   The Ternary Weight Channels construction uses the pair moment channels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L43-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L43-L62

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
variable {ι κ I : Type*}

theorem ThreeSum.TernaryWeightChannels.pair_moment_channels {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), pairWeight S T left right
      (fun i => (leftMoment k j).eval (fun _ => B i))
      (fun i => (rightMoment k j).eval (fun _ => C i)) Q)=
      ∑ b∈S, ∑ c∈T, if TernaryConvolution.Adds (left b) (right c) Q then
        (C c-B b)^k else 0 := by sorry
