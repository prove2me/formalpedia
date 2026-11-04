-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_fold_meets
-- name    : ThreeSum.LightCyclic.fold_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:07.063207+00:00
-- url     : https://prove2.me/theorems/49ce1603-b82d-44c9-8334-04e4963908e1
-- title:
--   Light Cyclic: fold meets
-- statement:
--   The Light Cyclic construction uses the fold meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L18-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L18-L53

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.fold_meets {pLinear : ℕ} (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} {as bs : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (ha : as.length ≤ p) (hb : bs.length ≤ p)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (hprod : ProductAt μ src n (padTo n as) (padTo n bs))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) = cyclic p as bs r) ∧
        SameOutside μ μ' dst p := by sorry
