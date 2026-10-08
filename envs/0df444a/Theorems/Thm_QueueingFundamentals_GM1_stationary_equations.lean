-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_stationary_equations
-- name    : QueueingFundamentals.GM1.stationary_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:02:33.905796+00:00
-- url     : https://prove2.me/theorems/ba24aedd-7756-4bc7-8fe6-27a652d08f8a
-- title:
--   Eqs. (5.51)–(5.53) — the G/M/1 arrival-point stationary equations
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ (mean $1/\lambda$, $\lambda > 0$) and exponential service at rate $\mu > 0$, and let $P = \{p_{ij}\}$ be the transition matrix (5.51) of the number in the system just before an arrival, built from the probabilities $b_k$ of (5.50).
--
--   Let $q = \{q_n\}$ be a probability vector ($q_n \ge 0$, $\sum_n q_n = 1$). Then $qP = q$ holds if and only if
--   $$
--   q_i = \sum_{k=0}^{\infty} q_{i+k-1} b_k \quad (i \ge 1), \qquad q_0 = \sum_{j=0}^{\infty} q_j \Big(1 - \sum_{k=0}^{j} b_k\Big).
--   $$
--
--   These are the equations (5.53) from which the book derives the characteristic equation $z = \beta(z)$.
--
--   **Formalization Note** Each equation asserts that the series converges to the stated value (`HasSum`).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.260, Eqs. (5.51)–(5.53)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eqs. (5.51)–(5.53): for a probability vector `q`, the stationary equations `qP = q` of the
arrival-point chain are equivalent to the equations (5.53). -/
theorem stationary_equations (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : HasSum q 1) :
    (∀ j, HasSum (fun i => q i * transitionProb A mu i j) (q j)) ↔
      ((∀ i, 1 ≤ i → HasSum (fun k => q (i + k - 1) * serviceProb A mu k) (q i)) ∧
        HasSum (fun j => q j * (1 - ∑ k ∈ Finset.range (j + 1), serviceProb A mu k)) (q 0)) := by sorry

end QueueingFundamentals.GM1
