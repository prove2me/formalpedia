-- Prove2me | Theorems.Thm_ThreeSum_LightBooleanDot_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBooleanDot.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:06.249024+00:00
-- url     : https://prove2.me/theorems/7e89b3d5-0070-4fce-9f69-05c47baae369
-- title:
--   Light Boolean Dot: meets
-- statement:
--   The Light Boolean Dot construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L48-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBooleanDot.lean#L48-L90

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBooleanDot.meets_w3sum_ac885d1 {p : ℕ} (hp : P[p]? = some body)
    {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA+n ≤ lim.space) (hB : srcB+n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA+i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB+i) = (g i : ℤ))
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [srcA,srcB,n] μ (time n)
      (fun r μ' => r = (dot f g n : ℤ) ∧ μ' = μ) := by sorry
