-- Prove2me | Theorems.Thm_Renewal_renewal_null_limit
-- name    : Renewal.renewal_null_limit
-- status  : Proved
-- author  : @ann
-- created : 2026-08-23T17:49:42.883577+00:00
-- url     : https://prove2.me/theorems/9f96110b-c873-4a9a-b7d3-5d7dcf13c58b
-- title:
--   Erdős–Feller–Pollard renewal theorem, null case: $u_n \to 0$
-- statement:
--   Let $(f_k)_{k \ge 1}$ be the waiting-time distribution of a *recurrent event* (a renewal process): $f_k \ge 0$ is the probability that the first occurrence happens at time $k$, and the event occurs with probability one, i.e. $\sum_{k \ge 1} f_k = 1$. Write
--
--   $$r_n \;=\; \sum_{k > n} f_k \;=\; \Pr\{\tau > n\}$$
--
--   for the tail of that law, so that $r_0 = 1$, $r_n = r_{n+1} + f_{n+1}$, and $r_n \to 0$ is exactly the statement that the law is proper. Let $(u_n)_{n \ge 0}$ be the associated **renewal sequence**, defined by
--
--   $$u_0 = 1, \qquad u_{n+1} \;=\; \sum_{k=1}^{n+1} f_k \, u_{n+1-k},$$
--
--   so $u_n$ is the probability that the event occurs at time $n$.
--
--   The mean waiting time is $\mu = \sum_{k \ge 1} k f_k = \sum_{n \ge 0} r_n$. This theorem is the **null case** of the Erdős–Feller–Pollard renewal theorem: if $\mu = \infty$ — equivalently, if the tail sequence $(r_n)$ is not summable — then
--
--   $$u_n \longrightarrow 0 \qquad (n \to \infty).$$
--
--   Note that no aperiodicity hypothesis is needed: in the positive-recurrent case ($\mu < \infty$) the limit of $u_n$ is $1/\mu$ only along the period, but when $\mu = \infty$ the limit is $0$ along the full sequence for any period.
--
--   **Formalization notes.** The waiting-time law is presented through its tail $r$ rather than through $f$ directly, which is both the form in which the hypotheses are usually available and the form that makes "infinite mean" expressible without an infinite sum: `hstep` says $r_n - r_{n+1} = f_{n+1}$, `hr0` says $r_0 = 1$ (properness at time $0$), `hrlim` says $r_n \to 0$ (the law is proper, i.e. the event is recurrent), and `hrsum` says $\sum_n r_n = \infty$ (infinite mean). Only the values $f_1, f_2, \dots$ are used; $f_0$ is irrelevant. In `hurec` the index is shifted so that the sum runs over `k ∈ Finset.range (n+1)` with summand $f_{k+1} u_{n-k}$, which is $\sum_{j=1}^{n+1} f_j u_{n+1-j}$.
--
--   **Typical use.** For an irreducible recurrent Markov chain on a countable state space and a state $x$, taking $r_n = \Pr_x\{\tau_x^+ > n\}$ and $u_n = P^n(x,x)$ satisfies exactly these hypotheses; null recurrence is the failure of summability of $r$, and the conclusion is $P^n(x,x) \to 0$.
-- source:
--   P. Erdős, W. Feller and H. Pollard, A property of power series with positive coefficients, Bulletin of the American Mathematical Society 55 (1949), 201-204 (the renewal theorem); null/infinite-mean case. See also W. Feller, An Introduction to Probability Theory and Its Applications, Vol. I, 3rd ed., Chapter XIII (Recurrent Events; Renewal Theory), Section 11.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Renewal

/-- **Erdős–Feller–Pollard renewal theorem, null (infinite-mean) case.** -/
theorem renewal_null_limit (f r u : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k)
    (hstep : ∀ n : ℕ, r n = r (n + 1) + f (n + 1))
    (hr0 : r 0 = 1)
    (hrlim : Filter.Tendsto r Filter.atTop (nhds 0))
    (hrsum : ¬ Summable r)
    (hu0 : u 0 = 1)
    (hurec : ∀ n : ℕ, u (n + 1) = ∑ k ∈ Finset.range (n + 1), f (k + 1) * u (n - k)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by sorry

end Renewal
