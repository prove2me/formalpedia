-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGlobalReceiptTransport_preparation_reads
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.preparation_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:11.9806+00:00
-- url     : https://prove2.me/theorems/171dc9ba-5aab-4f03-96ed-3fa3cab418ae
-- title:
--   preparation_reads
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L58-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L58-L94

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalReceiptTransport
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalReceiptTransport.preparation_reads {M b p K κ n free c : ℕ} [Fact p.Prime] {μ ν : ℕ→ℤ}
    (H : Receipt M b p K κ n free c μ ν) :
    let par := LightWeightedGlobalGlobalPrelude.params free
    let J := LightWeightedGlobalDimensions.J M b n (n^κ)
    let d := LightWeightedGlobalDimensions.dim M b p K n (n^κ)
    let q := p^d
    let menu := physical (backend free) d q J
    9≤par ∧ par+19≤scanFree M b p K κ n free+6 ∧ menu≤scanFree M b p K κ n free+6 ∧
    ν (par-9)=((n^κ:ℕ):ℤ) ∧ ν (par-8)=(LightWeightedGlobalDimensions.r M n:ℤ) ∧
    ν (par-7)=(J:ℤ) ∧ ν (par-5)=(q:ℤ) ∧ ν (par-3)=(menu:ℤ) ∧
    ν par=(Scales.inputBits n:ℤ) := by sorry
