-- Prove2me | Theorems.Thm_ThreeSumApsp_FromClaims_exists_solves_pair
-- name    : ThreeSumApsp.FromClaims.exists_solves_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:42.327195+00:00
-- url     : https://prove2.me/theorems/4f652ca2-505a-41bd-b4f9-66a16dc911d5
-- title:
--   From Claims: exists solves pair
-- statement:
--   Two programs, each with its slope and its constant, have one slope and one constant in common.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L72-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/RunningTimes/FromClaims/Bounds.lean#L72-L84

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem ThreeSumApsp.FromClaims.exists_solves_pair {prob₁ prob₂ : Problem} {dom₁ : prob₁.Inst → Prop}
    {dom₂ : prob₂.Inst → Prop} {X₁ : prob₁.Inst → ℝ} {X₂ : prob₂.Inst → ℝ}
    (h₁ : ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob₁ P b dom₁ fun x => K * X₁ x)
    (h₂ : ∃ (P : List Instr) (b : ℕ) (K : ℝ), 0 ≤ K ∧ Solves prob₂ P b dom₂ fun x => K * X₂ x)
    (hX₁ : ∀ x, dom₁ x → 1 ≤ X₁ x) (hX₂ : ∀ x, dom₂ x → 1 ≤ X₂ x) :
    ∃ (P₁ P₂ : List Instr) (b : ℕ) (K : ℝ),
      Solves prob₁ P₁ b dom₁ (fun x => K * X₁ x) ∧ Solves prob₂ P₂ b dom₂ (fun x => K * X₂ x) := by sorry
