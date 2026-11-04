-- Prove2me | Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
-- name    : ThreeSum.LightBooleanDot.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:58.190517+00:00
-- url     : https://prove2.me/theorems/4c1a1852-e10b-41a6-8419-ffa5f70e4659
-- title:
--   Light Boolean Dot: program meets
-- statement:
--   The Light Boolean Dot construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L94-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L94-L104

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBooleanDot.program_meets
    {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA+n ≤ lim.space) (hB : srcB+n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA+i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB+i) = (g i : ℤ))
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [srcA,srcB,n] μ (time n)
      (fun r μ' => r = (dot f g n : ℤ) ∧ μ' = μ) := by sorry
