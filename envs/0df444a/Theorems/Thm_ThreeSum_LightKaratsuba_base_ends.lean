-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_base_ends
-- name    : ThreeSum.LightKaratsuba.base_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:51.094773+00:00
-- url     : https://prove2.me/theorems/34d57f06-4bb2-43be-a753-496762f813fd
-- title:
--   Light Karatsuba: base ends
-- statement:
--   The Light Karatsuba construction uses the base ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L280-L296
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L280-L296

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightKaratsuba.base_ends {μ : ℕ → ℤ} {a b out work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + 1 ≤ lim.space) (hb : b + 1 ≤ lim.space)
    (hout : out + 2 ≤ lim.space) (hmul : |μ a * μ b| ≤ lim.word) :
    Ends lim P d baseBody ⟨frame [1, a, b, out, work], μ⟩ 12 fun σ' =>
      σ'.mem out = μ a * μ b ∧ σ'.mem (out + 1) = 0 ∧
        SameOutside μ σ'.mem out 2 := by sorry
