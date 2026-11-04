-- Prove2me | Theorems.Thm_ThreeSum_LightModuloCounts_meets_w3sum_ac885d1
-- name    : ThreeSum.LightModuloCounts.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:49:05.623583+00:00
-- url     : https://prove2.me/theorems/4371f406-fa28-4627-912e-23e7e2e5ec7e
-- title:
--   Light Modulo Counts: meets
-- statement:
--   The Light Modulo Counts construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightModuloCounts.lean#L50-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightModuloCounts.lean#L50-L200

import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e

set_option autoImplicit false
open ThreeSum ThreeSum.LightModuloCounts
open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightModuloCounts.meets_w3sum_ac885d1 {pMain pCapacity pHist pCyclic pResidues pEmod
    pHistogram pMultiply pHalf pLinear pFill pLookup : ℕ}
    (hmain : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup))
    (hcap : P[pCapacity]? = some LightCapacity.body)
    (hhist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    (hcount : P[pHistogram]? = some (LightHistogram.histogramBody pFill))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    (hlookup : P[pLookup]? = some LightLookupSum.body)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free := by sorry
