-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCleanupLayout_inputs
-- name    : ThreeSum.WeightedGlobalArenaCleanupLayout.inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:33:34.697505+00:00
-- url     : https://prove2.me/theorems/2d29f8cb-a6ea-42b0-a21e-c66a4cf3b2c3
-- title:
--   Weighted Global Arena Cleanup Layout: inputs
-- statement:
--   The Weighted Global Arena Cleanup Layout construction uses the inputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean#L78-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean#L78-L152

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_Inputs_finish
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCleanupLayout
open Light WeightedGlobalArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaCleanupLayout.inputs {lim : Limits} {d U free C aBase nA bBase nB cBase nC q L : ℕ}
    (μ : ℕ→ℤ) (A B Cv : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hend : finish free C≤lim.space)
    (hA : aBase+nA≤addr free C 6) (hB : bBase+nB≤addr free C 6)
    (hC : cBase+nC≤addr free C 6)
    (hBcap : 2*nB≤C) (hCcap : nB+3*nC+1≤C) (hCc : nC+1≤C)
    (hq : q≤C) (hL : L+1≤C)
    (hword : ((nB+nC+2^(L+1)+16 : ℕ) : ℤ)≤lim.word)
    (hscoreB : ((nB*nB+nB+q+16 : ℕ) : ℤ)≤lim.word)
    (hscoreC : ((nC*nC+nC+q+16 : ℕ) : ℤ)≤lim.word)
    (hkeysB : ∀ i<nB,keysB i<q) (hkeysC : ∀ i<nC,keysC i<q)
    (hreadKB : ∀ i<nB,μ (addr free C 4+i)=(keysB i : ℤ))
    (hreadKC : ∀ i<nC,μ (addr free C 5+i)=(keysC i : ℤ))
    (hboundA : ∀ i<nA,|A i|≤(U : ℤ))
    (hboundB : ∀ i<nB,|B i|≤(U : ℤ)) (hboundC : ∀ i<nC,|Cv i|≤(U : ℤ))
    (hreadA : ∀ i<nA,μ (aBase+i)=A i)
    (hreadB : ∀ i<nB,μ (bBase+i)=B i) (hreadC : ∀ i<nC,μ (cBase+i)=Cv i)
    (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hsortedB : ∀ i j,i<j→j<nB→B i<B j)
    (hsortedC : ∀ i j,i<j→j<nC→Cv i<Cv j)
    (hnB : nB<2^L) (hnC : nC<2^L) (hd : d+L+5≤lim.depth) :
    LightWeightedGlobalPreparedPostSelection.Inputs
      (layout free C aBase nA bBase nB cBase nC q L) lim d U L μ A B Cv keysB keysC := by sorry
