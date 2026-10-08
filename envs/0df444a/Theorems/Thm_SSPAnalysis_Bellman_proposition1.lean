-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_proposition1
-- name    : SSPAnalysis.Bellman.proposition1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:10:21.333036+00:00
-- url     : https://prove2.me/theorems/b94c46ef-84c4-42a6-9634-932eacc7d6a6
-- title:
--   Proposition 1 — Bellman contraction when all stationary policies are proper
-- statement:
--   Suppose Assumptions 1 and 2 hold and every stationary selector is proper. Then there are strictly positive weights $w_i$ and a factor $0\le\beta<1$ such that, on $X=\{x:x_1=0\}$,
--
--   $$\|T(x)-T(y)\|_\infty^w\le\beta\|x-y\|_\infty^w,\qquad \|z\|_\infty^w=\max_i\frac{|z_i|}{w_i}.$$
--
--   This identifies the contraction regime used as the starting point for the proper-policy part of Lemma 1.
--
--   **Formalization Note.** States use `Fin n` with state $1$ at index `0`. Stochastic transition rows are explicit. Compact control spaces are represented as compact metric carriers. The weights and contraction factor are existentially quantified after the model, as in the paper's claim for a given problem.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 585, Proposition 1 and weighted maximum norm immediately above it

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Filter Topology

/-- Proposition 1 (p. 585): if every stationary policy is proper, the
Bellman mapping contracts on X in a weighted maximum norm. -/
theorem proposition1 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    [∀ i, MetricSpace (U i)] (m : Model n U)
    (h1 : m.Assumption1) (h2 : m.Assumption2)
    (hall : ∀ μ : Selector U, m.IsProper μ) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧
        ∀ x ∈ X n, ∀ y ∈ X n,
          wNorm w (m.T x - m.T y) ≤ β * wNorm w (x - y) := by sorry

end SSPAnalysis.Bellman
