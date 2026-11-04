-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_program_meets
-- name    : ThreeSum.LightCyclic.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:34:44.155702+00:00
-- url     : https://prove2.me/theorems/a3ec2ecc-ab16-4ce3-83e9-ab5dbdcbde97
-- title:
--   Light Cyclic: program meets
-- statement:
--   The Light Cyclic construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L142-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCyclic.lean#L142-L162

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCyclic.program_meets
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
    Meets lim program 0 d [2^k, a, b, prod, dst, work, p] μ (combinedTime k p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j)) := by sorry
