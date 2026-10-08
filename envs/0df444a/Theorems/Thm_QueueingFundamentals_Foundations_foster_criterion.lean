-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_foster_criterion
-- name    : QueueingFundamentals.Foundations.foster_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:49:12.769692+00:00
-- url     : https://prove2.me/theorems/9ad500cc-c5b6-4aa2-9d9e-9f32b7850744
-- title:
--   Theorem 1.2 — Foster's criterion for positive recurrence
-- statement:
--   Let $P=\{p_{ij}\}$ be the transition matrix of an irreducible, aperiodic discrete-parameter Markov chain on $\{0,1,2,\dots\}$. Suppose there are numbers $x_j\ge0$ such that every series $\sum_j p_{ij}x_j$ converges and
--   $$\sum_{j=0}^{\infty}p_{ij}x_j\le x_i-1\quad(i\ne0),\qquad \sum_{j=0}^{\infty}p_{0j}x_j<\infty .$$
--   Then the chain is positive recurrent: every state $j$ is recurrent and has finite mean recurrence time $m_{jj}$.
--
--   This drift criterion (Foster, 1953) is the standard tool for proving that the imbedded Markov chains of queueing models, such as the M/G/1 queue, are positive recurrent and therefore have a steady-state distribution.
--
--   **Formalization Note** The book's condition $\sum_j p_{0j}x_j<\infty$ and the finiteness implied by the inequalities for $i\ne0$ are expressed together as the summability of every row series. Aperiodicity is kept as a hypothesis, as on the page, although the criterion holds without it.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.39, Theorem 1.2

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain

namespace QueueingFundamentals.Foundations

/-- Theorem 1.2 (p.39), Foster's criterion: an irreducible, aperiodic chain is positive recurrent
if there is a nonnegative `x` with `∑_j p_ij x_j ≤ x_i − 1` for `i ≠ 0` and
`∑_j p_0j x_j < ∞`. -/
theorem foster_criterion (P : TransitionMatrix) (hirr : P.Irreducible) (hap : P.Aperiodic)
    (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hsum : ∀ i, Summable (fun j => P.p i j * x j))
    (hdrift : ∀ i, i ≠ 0 → ∑' j, P.p i j * x j ≤ x i - 1) :
    P.PositiveRecurrent := by sorry

end QueueingFundamentals.Foundations
