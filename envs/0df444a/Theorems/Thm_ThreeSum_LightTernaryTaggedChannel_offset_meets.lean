-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryTaggedChannel_offset_meets
-- name    : ThreeSum.LightTernaryTaggedChannel.offset_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:30.099013+00:00
-- url     : https://prove2.me/theorems/7858cac2-7377-4b98-afca-b0fa031a3b72
-- title:
--   Light Ternary Tagged Channel: offset meets
-- statement:
--   The Light Ternary Tagged Channel construction uses the offset meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTaggedChannel.lean#L13-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTaggedChannel.lean#L13-L26

import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryTaggedChannel
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTaggedChannel
open Light TernarySignedLayout
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryTaggedChannel.offset_meets {p J i : ℕ} (hmain : P[p]?=some offsetBody) (μ : ℕ→ℤ)
    (hi : i<J+2) (hword : ((J+3 : ℕ) : ℤ)≤lim.word) :
    Meets lim P p d [i,J] μ 20
      (fun r ν => r=(offset J i : ℤ) ∧ ν=μ) := by sorry
