-- Prove2me | Theorems.Thm_ReedGGN_RenewalRep_renewal_equation
-- name    : ReedGGN.RenewalRep.renewal_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:24.680744+00:00
-- url     : https://prove2.me/theorems/05869d91-10db-4475-88ab-b6089e9cb77c
-- title:
--   (5.39) — the renewal function is finite and the unique locally bounded solution of M = F + M ∗ dF
-- statement:
--   Let $F$ be a service-time distribution: the distribution function of a probability measure $\mu$ on $[0,\infty)$ with finite mean $\int x\,d\mu(x)=1$. Let $M(t)=\sum_{n\ge1}F^{*n}(t)$ be its renewal function and $dM$ its renewal measure. Then:
--
--   1. $M$ is finite: $dM((-\infty,t])<\infty$ for every $t$;
--   2. $M$ solves the **renewal equation**
--   $$M(t)=F(t)+\int_0^t M(t-u)\,dF(u)\qquad\text{for } t\ge 0;$$
--   3. $M$ is its unique solution: every measurable function $m$ that is bounded on each interval $[0,T]$ and satisfies $m(t)=F(t)+\int_0^t m(t-u)\,dF(u)$ for all $t\ge 0$ coincides with $M$ on $[0,\infty)$.
--
--   The paper cites this from Ross (Exercise 3.4) as the characterization of $M$ used in Corollary 5.2.
--
--   **Formalization Note** The integral is over the closed interval $[0,t]$; at $t=0$ the equation reads $M(0)=F(0)+M(0)F(0)$, so $M(0)=F(0)/(1-F(0))$. Finiteness needs $F(0)<1$, which follows from mean $1$ and nonnegativity; the mean-$1$ hypothesis is otherwise unused. "Unique solution" is made explicit as uniqueness among measurable, locally bounded functions, on $[0,\infty)$; measurability makes the integrals meaningful.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 29, Eq. (5.39) (cited from Ross, Stochastic Processes, Exercise 3.4)

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory ProbabilityTheory

/-- (5.39), p. 29 (cited from Ross, Exercise 3.4). For a service law `μ` (probability measure
on `[0, ∞)` with mean `1`), the renewal function `M(t) = ∑_{n≥1} F^{∗n}(t)`
(a) is finite: `dM((-∞, t]) < ∞` for every `t`;
(b) solves the renewal equation `M(t) = F(t) + ∫_{[0,t]} M(t − u) dF(u)` for `t ≥ 0`;
(c) is its unique solution among measurable functions bounded on every `[0, T]`, on `[0, ∞)`. -/
theorem renewal_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1) :
    (∀ t : ℝ, renewalMeasure μ (Set.Iic t) < ⊤) ∧
    (∀ t : ℝ, 0 ≤ t →
      renewalFn μ t = cdf μ t + ∫ u in Set.Icc 0 t, renewalFn μ (t - u) ∂μ) ∧
    (∀ m : ℝ → ℝ, Measurable m → IsLocallyBounded m →
      (∀ t : ℝ, 0 ≤ t → m t = cdf μ t + ∫ u in Set.Icc 0 t, m (t - u) ∂μ) →
      Set.EqOn m (renewalFn μ) (Set.Ici 0)) := by sorry

end ReedGGN.RenewalRep
