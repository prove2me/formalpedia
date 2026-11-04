-- Prove2me | Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
-- name    : ThreeSum.LightPrimeChain.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:20:00.93468+00:00
-- url     : https://prove2.me/theorems/b09bc55f-4f57-408a-ab79-dcfe2d4b2738
-- title:
--   Procs: meets
-- statement:
--   Execute every level of the deterministic modulus chain, retaining every
--   prefix modulus and preserving all original cells below `free`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L189-L314
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean#L189-L314

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPrimeChain.Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC N aux s levels free maxMod U Y : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U levels ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+6 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y^(levels+1) ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,N,aux,s,levels,free] μ
      (time maxMod nA nB nC s U levels)
      (fun r μ' =>
        r = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) levels : ℤ) ∧
        (∀ i ≤ levels, μ' (free+i) = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) i : ℤ)) ∧
        Kept μ μ' free) := by sorry
