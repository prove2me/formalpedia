-- Prove2me | Theorems.Thm_ThreeSum_LightSharedReportingLoop_forSum_w3sum_ac885d1
-- name    : ThreeSum.LightSharedReportingLoop.forSum_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:07:40.192939+00:00
-- url     : https://prove2.me/theorems/f0c9aa85-a2fb-47c6-971d-f19d8fb86c57
-- title:
--   Light Shared Reporting Loop: for Sum
-- statement:
--   The Light Shared Reporting Loop construction uses the for Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingLoop.lean#L9-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingLoop.lean#L9-L65

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLoop
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingLoop
open Light

theorem ThreeSum.LightSharedReportingLoop.forSum_w3sum_ac885d1 {lim : Limits} {P : Program} {d : ℕ}
    {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (start : I 0 {σ with loc := Function.update σ.loc i 0})
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i=(j : ℤ) → I j σ →
      Ends lim P d body σ (b j) (fun σ' =>
        σ'.loc i=(j : ℤ) ∧ I (j+1) {σ' with loc := Function.update σ'.loc i ((j : ℤ)+1)}))
    (done : ∀ (σ : State), σ.loc i=(n : ℤ) → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i=(j : ℤ) → I j σ →
      hi.Safe lim σ ∧ hi.val σ=(n : ℤ))
    (hn : (n : ℤ) ≤ lim.word)
    (hT : (∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by sorry
