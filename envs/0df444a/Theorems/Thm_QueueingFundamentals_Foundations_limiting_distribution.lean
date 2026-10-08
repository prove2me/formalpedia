-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_limiting_distribution
-- name    : QueueingFundamentals.Foundations.limiting_distribution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:48:55.12811+00:00
-- url     : https://prove2.me/theorems/bd0fb68f-3e4c-4b51-8a4c-a62402771adc
-- title:
--   Theorem 1.1(c) — limiting probabilities equal the stationary distribution
-- statement:
--   Let $P=\{p_{ij}\}$ be the transition matrix of an irreducible, aperiodic and positive recurrent discrete-parameter Markov chain on $\{0,1,2,\dots\}$, with mean recurrence times $m_{jj}$ and stationary distribution $\pi_j=1/m_{jj}$ (Theorem 1.1(a)). Assume that all moments of this stationary distribution are finite, $\sum_j j^r\pi_j<\infty$ for every $r=0,1,2,\dots$. Then $\pi$ is a stationary probability vector and, for all states $i,j$,
--   $$\lim_{m\to\infty}p_{ij}^{(m)}=\pi_j=\frac{1}{m_{jj}} .$$
--   That is, the chain has a limiting probability distribution, independent of the initial state, equal to the stationary distribution.
--
--   **Formalization Note** The book's standing assumption before parts (b) and (c) ("when all moments of this stationary distribution are finite") is kept as a hypothesis. The book's additional word "ergodic" refers to its informal notion of ergodicity (time averages equal ensemble averages, p.36) and is not formalized; the statement is the limiting-distribution conclusion, which the book itself calls "the strongest condition, ergodicity is somewhat weaker" (p.39, directly after the theorem).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.39, Theorem 1.1(c)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain

open Filter Topology

namespace QueueingFundamentals.Foundations

/-- Theorem 1.1(c) (p.39), limiting-distribution part: if the chain is irreducible, aperiodic
and positive recurrent and all moments of its stationary distribution `π_j = 1/m_jj` are finite,
then `lim_{m→∞} p_ij^(m) = π_j` for all `i, j`, and this limit is the stationary distribution. -/
theorem limiting_distribution (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) (hpos : P.PositiveRecurrent)
    (hmom : ∀ r : ℕ,
      Summable (fun j : ℕ => (j : ℝ) ^ r * (P.meanRecurrenceTime j)⁻¹.toReal)) :
    P.IsStationaryDist (fun j => (P.meanRecurrenceTime j)⁻¹.toReal) ∧
      ∀ i j : ℕ, Tendsto (fun m : ℕ => P.stepProb m i j) atTop
        (𝓝 ((P.meanRecurrenceTime j)⁻¹.toReal)) := by sorry

end QueueingFundamentals.Foundations
