-- Prove2me | Theorems.Thm_ProjReflGrad_Weak_lemma_2_7
-- name    : ProjReflGrad.Weak.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:46.561806+00:00
-- url     : https://prove2.me/theorems/c900fa1a-b4fc-4709-8a19-9031e0d2f85a
-- title:
--   Lemma 2.7, p. 3 — nonnegative $a_{n+1}\le a_n-b_n$ forces $(a_n)$ bounded and $b_n\to0$
-- statement:
--   Let $(a_n)$ and $(b_n)$ be two nonnegative real sequences such that
--   $$a_{n+1}\le a_n-b_n\qquad\text{for all }n .$$
--   Then $(a_n)$ is bounded and $\lim_{n\to\infty}b_n=0$.
--
--   This elementary lemma turns the descent inequality (3.6) into boundedness of the iterates and vanishing of the steps.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 3, Lemma 2.7

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Weak

/-- Lemma 2.7 (Malitsky 2015, p. 3): if `(a_n)`, `(b_n)` are nonnegative real sequences with
`a_{n+1} ≤ a_n - b_n`, then `(a_n)` is bounded and `b_n → 0`. -/
theorem lemma_2_7 (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hab : ∀ n, a (n + 1) ≤ a n - b n) :
    Bornology.IsBounded (Set.range a) ∧ Filter.Tendsto b Filter.atTop (nhds 0) := by sorry

end ProjReflGrad.Weak
