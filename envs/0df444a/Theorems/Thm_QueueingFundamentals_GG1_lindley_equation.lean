-- Prove2me | Theorems.Thm_QueueingFundamentals_GG1_lindley_equation
-- name    : QueueingFundamentals.GG1.lindley_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:48:25.522892+00:00
-- url     : https://prove2.me/theorems/2b438a43-c2e7-43b2-af03-f52fc6efc87a
-- title:
--   Eq. (6.8) — Lindley's equation for the stationary G/G/1 delay
-- statement:
--   Consider the G/G/1 queue with interarrival distribution $A$ and service distribution $B$, both lifetime laws with finite means, $\mathrm E[T]>0$, and traffic intensity $\rho=\mathrm E[S]/\mathrm E[T]<1$. Let $U$ be the law of $S-T$ for independent $S\sim B$, $T\sim A$, as in (6.9). Then:
--
--   1. there is a stationary delay distribution, that is, a probability law $\nu$ such that if $W_q^{(n)}\sim\nu$ is independent of $S^{(n)}$ and $T^{(n)}$, then $W_q^{(n+1)}=\max(0,W_q^{(n)}+S^{(n)}-T^{(n)})\sim\nu$;
--   2. the CDF $W_q(t)$ of every stationary delay distribution satisfies Lindley's equation
--
--   $$
--   W_q(t)=\begin{cases}\displaystyle\int_{-\infty}^{t}W_q(t-x)\,dU(x) & (0\le t<\infty),\\[4pt] 0 & (t<0)\end{cases}
--   \;=\;-\int_{0}^{\infty}W_q(y)\,dU(t-y)\quad(0\le t<\infty).
--   $$
--
--   Lindley's equation is the integral equation of Wiener–Hopf type from which all the book's G/G/1 results follow; part 1 guarantees that it has a probability solution coming from the queue when $\rho<1$.
--
--   **Formalization Note** The book's sentence "In the steady state ($\rho<1$) … we find Lindley's equation" is stated as its two halves: existence of a stationary law of the recursion (part 1), and the equation for every such law (part 2). The stationary law is a fixed point of the law map of the recursion, not an arbitrary CDF satisfying the equation. The Stieltjes integral $-\int_0^\infty W_q(y)\,dU(t-y)$ is written as the integral of $W_q$ over $[0,\infty)$ against the law of $t-U$ (the minus sign accounts for $y\mapsto U(t-y)$ being decreasing). Integrals over $(-\infty,t]$ and $[0,\infty)$ include their endpoints.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.285, Eq. (6.8), for the recursion of p.284 and U of Eq. (6.9)

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- Lindley's equation (6.8) (p.285) for the G/G/1 queue. Let the interarrival times have law `A`
and the service times law `B` (lifetime laws with finite means), and let `ρ = E[S]/E[T] < 1`.
Then (i) a stationary delay distribution exists: a probability law `ν` that Lindley's recursion
`W_q^{(n+1)} = max(0, W_q^{(n)} + S^{(n)} − T^{(n)})` maps to itself; and (ii) the CDF
`W_q = cdfOf ν` of every stationary delay distribution satisfies
`W_q(t) = ∫_{−∞}^{t} W_q(t − x) dU(x) = −∫_0^∞ W_q(y) dU(t − y)` for `0 ≤ t < ∞` and
`W_q(t) = 0` for `t < 0`, where `U` is the law of `S − T` (6.9). The Stieltjes integral
`−∫_0^∞ W_q(y) dU(t − y)` is the integral of `W_q` over `[0, ∞)` against the law of `t − U`. -/
theorem lindley_equation (A B : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B)
    (hmeanA : 0 < meanOf A) (hρ : trafficIntensity A B < 1) :
    (∃ ν : Measure ℝ, IsStationaryDelay A B ν) ∧
    ∀ ν : Measure ℝ, IsStationaryDelay A B ν →
      ∀ t : ℝ,
        (0 ≤ t →
          cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) ∧
          cdfOf ν t = ∫ y in Set.Ici 0, cdfOf ν y ∂((diffLaw A B).map (fun x => t - x))) ∧
        (t < 0 → cdfOf ν t = 0) := by sorry

end QueueingFundamentals.GG1
