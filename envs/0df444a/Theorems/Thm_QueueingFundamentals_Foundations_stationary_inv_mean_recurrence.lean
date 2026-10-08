-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_stationary_inv_mean_recurrence
-- name    : QueueingFundamentals.Foundations.stationary_inv_mean_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:48:51.083242+00:00
-- url     : https://prove2.me/theorems/9cefd316-a336-47a0-a891-433f6f98bc6b
-- title:
--   Theorem 1.1(a) — the stationary distribution is π_j = 1/m_jj
-- statement:
--   Let $P=\{p_{ij}\}$ be the transition matrix of an irreducible, positive recurrent discrete-parameter Markov chain on $\{0,1,2,\dots\}$, and let $m_{jj}$ be the mean recurrence time of state $j$. Then
--
--   1. the vector $\pi_j=1/m_{jj}$ is a solution of the stationary equations
--   $$\pi=\pi P,\qquad \pi e=1,$$
--   with $\pi_j\ge0$; and
--   2. every nonnegative solution of these equations equals it: $\pi_j=1/m_{jj}$ for all $j$.
--
--   This identifies the stationary probability of a state with the long-run reciprocal of its mean return time, and it is the basic existence result for steady-state distributions used throughout the book.
--
--   **Formalization Note** The book's sentence asserts that a nondegenerate solution exists and that the solution vector is $\pi_j=1/m_{jj}$; the statement makes both halves explicit (existence of the probability solution $1/m_{jj}$ and uniqueness among probability vectors). The equation $\pi=\pi P$ is stated componentwise with convergent series.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.38–39, Theorem 1.1(a)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain

namespace QueueingFundamentals.Foundations

/-- Theorem 1.1(a) (pp.38–39): in an irreducible, positive recurrent chain the stationary
equations `π = πP`, `πe = 1` have a probability solution, and every such solution is
`π_j = 1/m_jj`. -/
theorem stationary_inv_mean_recurrence (P : TransitionMatrix) (hirr : P.Irreducible)
    (hpos : P.PositiveRecurrent) :
    P.IsStationaryDist (fun j => (P.meanRecurrenceTime j)⁻¹.toReal) ∧
      ∀ π : ℕ → ℝ, P.IsStationaryDist π → ∀ j, π j = (P.meanRecurrenceTime j)⁻¹.toReal := by sorry

end QueueingFundamentals.Foundations
