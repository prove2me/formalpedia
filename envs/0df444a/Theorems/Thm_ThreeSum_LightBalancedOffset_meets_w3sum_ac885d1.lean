-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedOffset_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBalancedOffset.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:32:14.398303+00:00
-- url     : https://prove2.me/theorems/0094f69b-1d71-4bdf-ba35-2c7a82ac3aa7
-- title:
--   Light Balanced Offset: meets
-- statement:
--   The Light Balanced Offset construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L45-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L45-L77

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4

set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBalancedOffset.meets_w3sum_ac885d1 {pMain pCyclic pMinimum pMultiply pHalf pLinear pFill : ℕ}
    (hmain : P[pMain]? = some (body pCyclic pMinimum))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (hminimum : P[pMinimum]? = some LightMinimum.body)
    (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a+2^k ≤ work) (hbf : b+2^k ≤ work)
    (hpf : prod+2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+3 ≤ lim.depth) :
    Meets lim P pMain d [2^k,a,b,prod,dst,work,p] μ (time k p)
      fun r μ' => r = (offset F H : ℤ) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by sorry
