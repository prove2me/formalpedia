-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_arrival_times_order_statistics
-- name    : ServiceParts.NonstatPalm.arrival_times_order_statistics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:56:54.925102+00:00
-- url     : https://prove2.me/theorems/50219018-f7e3-414e-a493-1f212c836fe3
-- title:
--   Theorem 12 — given N(t) = n, the demand epochs are order statistics of n i.i.d. draws from F = m(x)/m(t)
-- statement:
--   Consider the single-location model with nonstationary Poisson demand of rate $\lambda$, mean function $m$, and time-dependent resupply times. Fix $t$ with $m(t) > 0$ and let $F$ be the distribution function
--   $$F(x) = \begin{cases} 0, & x < 0,\\ m(x)/m(t), & 0 \le x < t,\\ 1, & x \ge t.\end{cases}$$
--   Let $\mu$ be the probability measure on $\mathbb R$ with distribution function $F$, and let $V_1, \dots, V_n$ be independent with law $\mu$, with order statistics $V_{(1)} \le \cdots \le V_{(n)}$. Then, for every $n$ and every measurable $A \subseteq \mathbb R^n$,
--   $$P\bigl(N(t) = n,\ (T_0, \dots, T_{n-1}) \in A\bigr) = P\bigl(N(t) = n\bigr)\, P\bigl((V_{(1)}, \dots, V_{(n)}) \in A\bigr).$$
--   That is, conditionally on $N(t) = n$, the demand epochs in $[0,t]$ have the same distribution as the order statistics of $n$ independent random variables with distribution function $F$.
--
--   This is the nonstationary counterpart of the uniform order-statistics property of a Poisson process, and it is the step on which the proof of Theorem 13 rests.
--
--   **Formalization Note** The book writes $F(x)$ only for $x \ge 0$; $F(x) = 0$ for $x < 0$ is added, since demands occur at nonnegative times. The hypothesis $m(t) > 0$ makes $F$ well defined; when $m(t) = 0$ there are almost surely no demands in $[0,t]$ and the book's $F$ is $0/0$. The measure $\mu$ is quantified universally over probability measures with distribution function $F$; there is exactly one. The order statistics are obtained by sorting the vector $(V_1, \dots, V_n)$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 216, Theorem 12

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem arrival_times_order_statistics {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (hm : 0 < S.meanFn t) (n : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ (Set.Iic x) = ENNReal.ofReal (S.arrivalCdf t x))
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.demandCount t ω = n} ∩ {ω | (fun i : Fin n => S.epoch (i : ℕ) ω) ∈ A}) =
      P {ω | S.demandCount t ω = n} *
        Measure.pi (fun _ : Fin n => μ) {x : Fin n → ℝ | x ∘ Tuple.sort x ∈ A} := by sorry

end ServiceParts.NonstatPalm
