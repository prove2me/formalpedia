-- Prove2me | Theorems.Thm_ThreeSum_ModuloRuntime_meets_bounded
-- name    : ThreeSum.ModuloRuntime.meets_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:54.126433+00:00
-- url     : https://prove2.me/theorems/a966cac0-9e76-4fff-a837-d6e93b557020
-- title:
--   Modulo Runtime: meets bounded
-- statement:
--   Uniform invocation of the actual modular-counting program.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloRuntime.lean#L55-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloRuntime.lean#L55-L78

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface

theorem ThreeSum.ModuloRuntime.meets_bounded {lim : Light.Limits} {P : Light.Program} {d pMain : ℕ}
    (C : LightModuloCounts.Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p maxMod N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p) (hm : p ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ
      (time maxMod nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Light.Kept μ μ' free) := by sorry
