-- Prove2me | Theorems.Thm_QZeroSum19_GK_exp_le_one_add_add_sq
-- name    : QZeroSum19.GK.exp_le_one_add_add_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:32.615651+00:00
-- url     : https://prove2.me/theorems/f4cd357e-6366-4031-a6fb-a6a36396270f
-- title:
--   Proof of Lemma 1, p. 4 — e^x ≤ 1 + x + 3x²/4 for all x ∈ [−1, 1]
-- statement:
--   For every real $x$ with $-1\le x\le 1$,
--   $$e^x\le 1+x+\tfrac34x^2 .$$
--
--   The proof of Lemma 1 applies this to $x=\eta(A_{ia}-A_{bj})$, which lies in $[-1,1]$ when the entries of $A$ lie in $[-1,1]$ and $\eta\le 1/2$, to bound the expected growth of the potential.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 4, proof of Lemma 1

import Mathlib

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 4: `e^x ≤ 1 + x + 3x²/4` for all `x ∈ [−1, 1]`. -/
theorem exp_le_one_add_add_sq (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.exp x ≤ 1 + x + 3 * x ^ 2 / 4 := by sorry

end QZeroSum19.GK
