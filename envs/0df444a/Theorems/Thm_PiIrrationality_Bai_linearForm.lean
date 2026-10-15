-- Prove2me | Theorems.Thm_PiIrrationality_Bai_linearForm
-- name    : PiIrrationality.Bai.linearForm
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:55:13.685539+00:00
-- url     : https://prove2.me/theorems/2d917b02-56cd-4da8-ab70-8f21dd7cdd5d
-- title:
--   Bai's linear forms $M_nJ_n=U_n+V_n\pi$ at exponents (1857, 3714, 5570)
-- statement:
--   For every $n\ge 1$ there are integers $U_n,V_n$ with
--   $$M_nJ_n=U_n+V_n\pi,\qquad V_n=-\tfrac14\,M_n\,25^n\,2^{3716n}\,\mathrm{coef}_n ,$$
--   where $J_n$, $M_n$ and $\mathrm{coef}_n$ are the objects of the Definition `PiIrrationality_BaiForms`.
--
--   Role: the arithmetic half of Bai's bound; it makes $M_nJ_n$ an integer linear form in $1,\pi$ with an explicit $\pi$-coefficient.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, Proposition 2.7 (with Lemmas 2.1-2.6), at (a,b,c) = (1857,3714,5570)

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem PiIrrationality.Bai.linearForm (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ, (PiIrrationality.Bai.M n : ℂ) * PiIrrationality.Bai.J n =
        (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
      (V : ℝ) = -(PiIrrationality.Bai.M n * 25 ^ n * 2 ^ (3716 * n) *
        (PiIrrationality.Bai.coef n : ℝ) / 4) := by
  sorry
