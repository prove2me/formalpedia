-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalReceiptTransport_preparation_reads
-- name    : ThreeSum.WeightedGlobalGlobalReceiptTransport.preparation_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:59:42.99607+00:00
-- url     : https://prove2.me/theorems/3e0eb73d-d124-4422-b906-10f33f20d8f4
-- title:
--   Weighted Global Global Receipt Transport: preparation reads
-- statement:
--   All global-header reads made by the actual per-color preparation are
--   consequences of the initialized ten-cell header and five-cell scales.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L58-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L58-L94

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalReceiptTransport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalGlobalReceiptTransport.preparation_reads {M b p K κ n free c : ℕ} [Fact p.Prime] {μ ν : ℕ→ℤ}
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
