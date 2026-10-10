-- Prove2me | Theorems.Thm_QueueBandit_LateLower_fact_1
-- name    : QueueBandit.LateLower.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:50.029566+00:00
-- url     : https://prove2.me/theorems/b10bc481-11d5-4796-8c0b-04c160bd3d10
-- title:
--   Fact 1, p. 42 — if Σ_{m≤n} a_m ≥ C log n eventually, then a_n ≥ C/(2n) infinitely often
-- statement:
--   Let $(a_n)_{n\ge1}$ be a sequence of real numbers, $C>0$ and $N_0\in\mathbb N$. If
--   $$\sum_{m=1}^{n}a_m\;\ge\;C\log n\qquad\text{for all } n\ge N_0,$$
--   then $a_n\ge \dfrac{C}{2n}$ for infinitely many $n$.
--
--   This converts a logarithmic lower bound on cumulative queue-regret into an infinitely-often lower bound of order $1/t$ on the queue-regret itself, the last step in the proof of Theorem 3.
--
--   **Formalization Note** The paper states Fact 1 for bounded sequences. Boundedness is dropped: the proof uses only the finitely many terms $a_1,\dots,a_{N_1}$, and the application to $a_t=\sum_u\Psi_u(t)$ has no uniform bound. The statement for every real sequence is stronger than the printed one. "Infinitely often" is `∃ᶠ n in atTop`.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 42, Fact 1

import Mathlib

open Finset Filter

namespace QueueBandit.LateLower

/-- Fact 1 (p. 42), for every real sequence: if C > 0 and Σ_{m=1}^n a_m ≥ C log n for all
n ≥ N₀, then a_n ≥ C/(2n) for infinitely many n. -/
theorem fact_1 (a : ℕ → ℝ) (C : ℝ) (hC : 0 < C) (N₀ : ℕ)
    (hsum : ∀ n : ℕ, N₀ ≤ n → C * Real.log n ≤ ∑ m ∈ Icc 1 n, a m) :
    ∃ᶠ n : ℕ in atTop, C / (2 * (n : ℝ)) ≤ a n := by sorry

end QueueBandit.LateLower
