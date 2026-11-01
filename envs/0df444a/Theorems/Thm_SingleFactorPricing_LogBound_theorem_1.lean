-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_theorem_1
-- name    : SingleFactorPricing.LogBound.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:08.662016+00:00
-- url     : https://prove2.me/theorems/5cc25d2c-5ce9-4d5e-98d6-05bd78dfc41a
-- title:
--   Theorem 1, p.4 — $\bar{\mathcal R}\le(1+\ln(q_{\max}/q_{\min}))\mathcal R^f$ under A0–A1, and the constant is tight
-- statement:
--   A firm sells a finite nonempty set $N$ of products to customer types distributed according to a probability measure $\mu$. Let $f$ be a positive vector, let $\bar p$ be a selection of optimal prices, and let
--
--   $$
--   \beta=1+\ln(q_{\max}/q_{\min}),
--   $$
--
--   where $q_{\min}$ and $q_{\max}$ are the infimum and supremum of the ratios $\bar p_{t,i}/f_i$.
--
--   1. **Bound.** If A0 and A1 hold (with non-negative demand, the regularity in the type, and $q_{\min}>0$), then
--
--   $$
--   \bar{\mathcal R}\le\beta\,\mathcal R^f .
--   $$
--
--   2. **Exact tightness.** For every $\rho>1$ there is an instance with one product, $f=1$, $q_{\min}=1$, $q_{\max}=\rho$, $\mathcal R^f>0$ and $\bar{\mathcal R}=(1+\ln\rho)\,\mathcal R^f$.
--   3. **Best constant over finite instances.** For every $\rho>1$ and every $c<1+\ln\rho$ there is an instance with one product, $f=1$, finitely many types with weights $\theta_j>0$ summing to one, $q_{\min}=1$, $q_{\max}=\rho$, $\mathcal R^f>0$ and $c\,\mathcal R^f<\bar{\mathcal R}$.
--
--   The theorem bounds the loss from replacing personalized prices by a one-dimensional pricing policy, with uniform pricing as the case $f=e$, in terms of how far the optimal prices are from a multiple of $f$. Since $\mathcal R^f\le\mathcal R^*\le\bar{\mathcal R}$, it also bounds both the performance of single-factor heuristics and the value of personalization.
--
--   **Formalization Note** With finitely many types, $\mathcal R^f>0$ and $q_{\min}<q_{\max}$, equality in the bound is impossible, while the paper's instance has a continuum of types. Items 2 and 3 are the two meanings of "tight", and neither implies the other.
--
--   Differences from the source:
--   - generalization: finitely many types $M$ with weights $\theta_j>0$ → any probability space $(T,\mu)$ of types; reason: the remark on p.5 extends the result to continuous types; $T=$ `Fin m` with `KallMayerSLP.ICC.discreteLaw θ id` is the printed case
--   - encoding: $N=\{1,\dots,n\}$ → any finite nonempty type `N`; reason: the same finite sets up to relabelling
--   - generalization: $\mathcal R^f$ a maximum → `IsLUB` of $R(qf)$ over $q>0$; reason: equal to the maximum when it exists; also covers a supremum that is not attained
--   - generalization: $q_{\min}$, $q_{\max}$ a min and a max → `IsGLB` and `IsLUB` of the ratios, with $0<q_{\min}$; reason: they equal the min and max for finite $T$, where A0 gives $0<q_{\min}$; for general $T$ this is the condition of p.5
--   - reading: "the bound is tight", stated for finitely many types and shown on a continuum → clause (B), exact tightness on a type space, and clause (C), best constant over finite instances; reason: equality is impossible for finitely many types once $q_{\min}<q_{\max}$ and $\mathcal R^f>0$; neither clause implies the other
--   - reading: the tight instance's tail has total mass $k$ → clause (B) requires a probability measure; reason: §2 requires $\sum_j\theta_j=1$; the instance puts the factor $k$ in each type's demand (milestone `tight_instance`), with the paper's aggregate demand
--   - encoding: $\mathcal R^*_j=\max_{p\ge0}R_j(p)$ → $R_t(\bar p_t)$ with the optimality of $\bar p$ in `AssumptionA0`; reason: the same value
--   - encoding: all demand functions are non-negative → non-negativity at $p\ge0$; reason: prices range over $p\ge0$ in the paper
--   - encoding: finite sums, no regularity stated → hypotheses on measurability of $\bar p$ and integrability of the demands; reason: automatic for finitely many types; they rule out junk Bochner integrals only
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, Theorem 1, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_personalizedProfit
import Definitions.Def_SingleFactorPricing_LogBound_LogBoundInstance
import Definitions.Def_KallMayerSLP_ICC_discreteLaw
universe u v

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Theorem 1.** Gallego, Berbeglia, arXiv:2102.03038v2, Theorem 1, p.4: "Suppose that A0 and A1
hold. Then `R̄ ≤ βRᶠ` where `β := 1 + ln(q_max/q_min)`. Moreover, the bound is tight."

Three clauses:
* **(A) bound**, for every finite nonempty product set, every probability space of types, every
  positive `f` and every selection `pbar` of optimal prices;
* **(B) exact tightness**: for each `ρ > 1`, an instance with `q_min = 1`, `q_max = ρ`, `0 < Rᶠ` and
  `R̄ = (1 + ln ρ) Rᶠ`;
* **(C) best constant over finite instances**: for each `ρ > 1` and `c < 1 + ln ρ`, an instance with
  finitely many types, weights `θ`, `q_min = 1`, `q_max = ρ`, `0 < Rᶠ` and `c Rᶠ < R̄`.

**Formalization Note.** The paper states the theorem for finitely many types, which is
`T = Fin m` and `μ = KallMayerSLP.ICC.discreteLaw θ id` (`∑ⱼ θⱼ • δⱼ`) in (A), and remarks on p.5 that it also holds for
continuous types. Its tight instance on p.4 has a continuum of types. With finitely many types and
`0 < Rᶠ`, `q_min < q_max`, equality is impossible, so "tight" is given both meanings, (B) and (C),
neither of which implies the other. `q_min`, `q_max` and `Rᶠ` are fixed by `LogBoundInstance`
through `IsGLB`, `IsLUB`, `IsLUB`, so (B) and (C) fix the true ratio `ρ`, not a bound on it. -/
theorem theorem_1 :
    (∀ (N : Type u) [Fintype N] [Nonempty N] (T : Type v) [MeasurableSpace T] (μ : Measure T)
        [IsProbabilityMeasure μ] (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ)
        (qmin qmax Rf : ℝ),
        LogBoundInstance μ d f pbar qmin qmax Rf →
          personalizedProfit μ d pbar ≤ (1 + Real.log (qmax / qmin)) * Rf) ∧
      (∀ ρ : ℝ, 1 < ρ →
        ∃ (T : Type) (_ : MeasurableSpace T) (μ : Measure T) (d : T → (Fin 1 → ℝ) → Fin 1 → ℝ)
          (pbar : T → Fin 1 → ℝ) (Rf : ℝ),
          IsProbabilityMeasure μ ∧ LogBoundInstance μ d (fun _ => 1) pbar 1 ρ Rf ∧ 0 < Rf ∧
            personalizedProfit μ d pbar = (1 + Real.log ρ) * Rf) ∧
      (∀ ρ c : ℝ, 1 < ρ → c < 1 + Real.log ρ →
        ∃ (m : ℕ) (θ : Fin m → ℝ) (d : Fin m → (Fin 1 → ℝ) → Fin 1 → ℝ)
          (pbar : Fin m → Fin 1 → ℝ) (Rf : ℝ),
          (∀ j, 0 < θ j) ∧ ∑ j, θ j = 1 ∧
            LogBoundInstance (KallMayerSLP.ICC.discreteLaw θ id) d (fun _ => 1) pbar 1 ρ Rf ∧ 0 < Rf ∧
            c * Rf < personalizedProfit (KallMayerSLP.ICC.discreteLaw θ id) d pbar) := by sorry

end SingleFactorPricing.LogBound
