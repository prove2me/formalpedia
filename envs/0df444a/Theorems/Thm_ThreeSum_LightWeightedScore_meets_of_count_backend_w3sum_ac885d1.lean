-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedScore_meets_of_count_backend_w3sum_ac885d1
-- name    : ThreeSum.LightWeightedScore.meets_of_count_backend_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:43.539867+00:00
-- url     : https://prove2.me/theorems/4d22bc7b-83a0-4ea3-adf2-1b7161cb3bc8
-- title:
--   Light Weighted Score: meets of count backend
-- statement:
--   The Light Weighted Score construction uses the meets of count backend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedScore.lean#L104-L209
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedScore.lean#L104-L209

import Definitions.Def_Submission_ThreeSum_WeightedScore
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightWeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedScore
open Light WeightedModuli WeightedScore LightResidues
variable {lim : Limits} {P : Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightWeightedScore.meets_of_count_backend_w3sum_ac885d1 {pMain pCount pJoint pEmod : ℕ}
    (hmain : P[pMain]? = some (body pCount pJoint))
    (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod countTime : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free) (hN : N ≤ lim.space)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word)
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod)
    (hcount : ∀ (ν : ℕ → ℤ) (p : ℕ), Kept μ ν free → 0 < p → p ≤ maxMod →
      Meets lim P pCount (d+1) [a,b,c,nA,nB,nC,p,N,free] ν countTime
        (fun r ν' => r = (ModuloCounts.count p nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept ν ν' free)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ (time countTime s maxMod)
      fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free := by sorry
