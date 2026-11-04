-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
-- name    : ThreeSum.LightKaratsuba.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:01.337532+00:00
-- url     : https://prove2.me/theorems/a225c79c-0c68-4e3d-8d46-63ae118c4584
-- title:
--   Light Karatsuba: program meets
-- statement:
--   The Light Karatsuba construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L649-L660
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L649-L660

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}

theorem ThreeSum.LightKaratsuba.program_meets (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (wordBound (2 ^ k) U : ℤ) ≤ lim.word)
    (d : ℕ) (hd : d + k + 1 ≤ lim.depth) :
    Meets lim program 0 d [2 ^ k, a, b, out, work] μ (time k)
      (fun _ μ' => Result μ out (2 ^ k) work as bs μ') := by sorry
