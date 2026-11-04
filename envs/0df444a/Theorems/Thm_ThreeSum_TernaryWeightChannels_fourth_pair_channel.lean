-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightChannels_fourth_pair_channel
-- name    : ThreeSum.TernaryWeightChannels.fourth_pair_channel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:14.00456+00:00
-- url     : https://prove2.me/theorems/675c3593-7aec-498d-b9a9-864268c9feaa
-- title:
--   Ternary Weight Channels: fourth pair channel
-- statement:
--   The Ternary Weight Channels construction uses the fourth pair channel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L79-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L79-L91

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
variable {ι κ I : Type*}

theorem ThreeSum.TernaryWeightChannels.fourth_pair_channel {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (L : ι→I→ℤ) (R : κ→I→ℤ) (a b c d : I) (Q : TritWord N) :
    pairWeight S T left right (productWeight L a b) (productWeight R c d) Q=
      ∑ i∈S, ∑ j∈T, if TernaryConvolution.Adds (left i) (right j) Q then
        L i a*L i b*R j c*R j d else 0 := by sorry
