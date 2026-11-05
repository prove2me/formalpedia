-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalColorPreparationProof_build_ends
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof.build_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:58:17.295837+00:00
-- url     : https://prove2.me/theorems/2f9715ce-2b36-432c-bdc8-dbe09893fdb5
-- title:
--   build_ends
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L205-L396
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L205-L396

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof.build_ends {lim : Limits} {radix n U R J q menu depth src params row free : ℕ}
    (μ : ℕ→ℤ) (A B C : List ℤ) (hb : 1<radix)
    (bounds : Bounds lim radix n U J depth)
    (hparams : params+19≤free) (hparams9 : 9≤params)
    (hspace : arenaFree free n (width n) A.length B.length C.length J U≤lim.space)
    (hR : (R:ℤ)≤lim.word) (hq : (q:ℤ)≤lim.word) (hmenu : (menu:ℤ)≤lim.word)
    (hUread : μ (params-9)=(U:ℤ)) (hRread : μ (params-8)=(R:ℤ))
    (hJread : μ (params-7)=(J:ℤ)) (hqread : μ (params-5)=(q:ℤ))
    (hmenuread : μ (params-3)=(menu:ℤ)) (hbits : μ params=(Scales.inputBits n:ℤ))
    (hAread : ∀i<A.length, μ (LightTernaryColorPrelude.av free n+i)=A.getD i 0)
    (hBread : ∀i<B.length, μ (LightTernaryColorPrelude.bv free n+i)=B.getD i 0)
    (hCread : ∀i<C.length, μ (LightTernaryColorPrelude.cv free n+i)=C.getD i 0)
    (hA : ∀z∈A, |z|≤(U:ℤ)) (hB : ∀z∈B, |z|≤(U:ℤ)) (hC : ∀z∈C, |z|≤(U:ℤ))
    (ha : A.length≤n) (hbLen : B.length≤n) (hc : C.length≤n) :
    Ends lim (program radix) depth (buildBody radix)
      ⟨frame [src,n,params,row,free,free,LightTernaryColorPrelude.av free n,A.length,
        LightTernaryColorPrelude.bv free n,B.length,LightTernaryColorPrelude.cv free n,C.length],μ⟩
      (buildTime A.length B.length C.length J U)
      (fun σ=>σ.loc 0=(headerAt free n (width n):ℤ) ∧
        Built μ σ.mem free n U R J q menu radix A B C) := by sorry
