-- Prove2me | Theorems.Thm_ThreeSum_LightKaratsuba_recurse_ends_w3sum_ac885d1
-- name    : ThreeSum.LightKaratsuba.recurse_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:02.982731+00:00
-- url     : https://prove2.me/theorems/dce645cf-c351-48da-8eb9-4895247b771b
-- title:
--   Light Karatsuba: recurse ends
-- statement:
--   The Light Karatsuba construction uses the recurse ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L436-L571
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean#L436-L571

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
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
set_option maxHeartbeats 2000000

theorem ThreeSum.LightKaratsuba.recurse_ends_w3sum_ac885d1 (C : Procs P pSelf pHalf pLinear pFill)
    {d k m a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hmPow : m = 2 ^ k) (hw : (lim.space : ℤ) ≤ lim.word)
    (hAlen : as.length = 2 * m) (hBlen : bs.length = 2 * m)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 * m ≤ work) (hbf : b + 2 * m ≤ work)
    (hof : out + 2 * (2 * m) ≤ work) (hspace : work + 8 * (2 * m) ≤ lim.space)
    (hword : (wordBound (2 * m) U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (ih : ∀ (a' b' out' work' U' : ℕ) (as' bs' : List ℤ) (μ' : ℕ → ℤ),
      as'.length = m → bs'.length = m → Seg μ' a' as' → Seg μ' b' bs' →
      CoeffBound as' (U' : ℤ) → CoeffBound bs' (U' : ℤ) →
      a' + m ≤ work' → b' + m ≤ work' → out' + 2 * m ≤ work' →
      work' + 8 * m ≤ lim.space → (wordBound m U' : ℤ) ≤ lim.word →
      Meets lim P pSelf (d + 1) [m, a', b', out', work'] μ' (time k)
        (fun _ μ'' => Result μ' out' m work' as' bs' μ'')) :
    Ends lim P d (recurseBody pSelf pHalf pLinear pFill)
      ⟨frame [2 * m, a, b, out, work], μ⟩ (time (k + 1) - 4)
      (fun σ' => Result μ out (2 * m) work as bs σ'.mem) := by sorry
