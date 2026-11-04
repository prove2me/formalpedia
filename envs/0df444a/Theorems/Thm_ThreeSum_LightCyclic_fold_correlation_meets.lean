-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_fold_correlation_meets
-- name    : ThreeSum.LightCyclic.fold_correlation_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:10.742818+00:00
-- url     : https://prove2.me/theorems/ce076c97-0208-489b-a410-d07e227d0450
-- title:
--   Light Cyclic: fold correlation meets
-- statement:
--   The Light Cyclic construction uses the fold correlation meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L55-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L55-L76

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.fold_correlation_meets {pLinear : ℕ}
    (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (hprod : ProductAt μ src n (padTo n (vector p F))
      (padTo n (vector p (fun z => H (-z)))))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧ SameOutside μ μ' dst p := by sorry
