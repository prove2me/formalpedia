-- Prove2me | Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
-- name    : ThreeSum.LightModuloCounts.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:48:43.860791+00:00
-- url     : https://prove2.me/theorems/095886ff-7952-4cb9-98ed-569822807e1c
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightModuloCounts.lean#L226-L243
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightModuloCounts.lean#L226-L243

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

theorem ThreeSum.LightModuloCounts.Procs.meets {pMain : ℕ} (C : Procs P pMain)
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
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free) := by sorry
