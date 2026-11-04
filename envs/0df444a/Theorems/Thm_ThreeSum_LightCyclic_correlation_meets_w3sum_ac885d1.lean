-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_correlation_meets_w3sum_ac885d1
-- name    : ThreeSum.LightCyclic.correlation_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:10.831223+00:00
-- url     : https://prove2.me/theorems/389ae1ac-a742-420e-a978-8aba840d3059
-- title:
--   Light Cyclic: correlation meets
-- statement:
--   The Light Cyclic construction uses the correlation meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L86-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L86-L128

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.correlation_meets_w3sum_ac885d1 {pThis pMultiply pHalf pLinear pFill : ℕ}
    (hThis : P[pThis]? = some (body pMultiply pLinear))
    (C : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    Meets lim P pThis d [2^k, a, b, prod, dst, work, p] μ (combinedTime k p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by sorry
