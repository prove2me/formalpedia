-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_join_ends_w3sum_ac885d1
-- name    : ThreeSum.LightKaratsuba.join_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:56.146604+00:00
-- url     : https://prove2.me/theorems/135ff381-97fa-47d4-93f0-1bdf4bbc3288
-- title:
--   Light Karatsuba: join ends
-- statement:
--   The Light Karatsuba construction uses the join ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L143-L272
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L143-L272

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
variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}

theorem ThreeSum.LightKaratsuba.join_ends_w3sum_ac885d1 (hLinear : P[pLinear]? = some LightArray.linearBody)
    (hFill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {n half a b out work U : ℕ} {r : ℤ}
    (hn : 0 < n) (hhalf : 2 * half = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hout : out + 2 * n ≤ work) (hwork : work + 3 * n ≤ lim.space)
    (hword : 10 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (work + i)| ≤ U ∧ |μ (work + n + i)| ≤ U ∧
      |μ (work + 2 * n + i)| ≤ U)
    (hd : d < lim.depth) :
    Ends lim P d (joinBody pLinear pFill)
      ⟨frame [n, a, b, out, work, half, r], μ⟩ (joinTime n) fun σ' =>
      (∀ j < 2 * n, σ'.mem (out + j) = joined μ work n half j) ∧
        KeptBut μ σ'.mem work out (2 * n) := by sorry
