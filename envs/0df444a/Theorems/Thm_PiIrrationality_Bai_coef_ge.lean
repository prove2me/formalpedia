-- Prove2me | Theorems.Thm_PiIrrationality_Bai_coef_ge
-- name    : PiIrrationality.Bai.coef_ge
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:56:31.196784+00:00
-- url     : https://prove2.me/theorems/1f388d5f-1e82-4f99-95de-85efbce488bc
-- title:
--   Lower bound $\mathrm{coef}_n\ge e^{15979.974204227497\,n}$ for large $n$
-- statement:
--   There is $N$ such that for all $n\ge N$,
--   $$\exp(15979.974204227497\,n)\le\mathrm{coef}_n .$$
--
--   Role: bounds $|V_n|$ from below, needed for the ratio $|\Lambda_n|/|V_n|$ in Hata's index selection.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, (4.11)-(4.12)

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Exp

theorem PiIrrationality.Bai.coef_ge :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (15979.974204227497 * (n : ℝ)) ≤ (PiIrrationality.Bai.coef n : ℝ) := by
  sorry
