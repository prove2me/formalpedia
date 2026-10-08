-- Prove2me | Theorems.Thm_StoneRegression_Quantile_theorem_3
-- name    : StoneRegression.Quantile.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:45.994627+00:00
-- url     : https://prove2.me/theorems/92bd978b-4a58-40c1-b5f1-7c45e0120d08
-- title:
--   Theorem 3, p. 604 — consistent probability weights give (L̂ₙ − L)⁻ → 0 and (Ûₙ − U)⁺ → 0, in probability and in Lʳ
-- statement:
--   Let $\{W_n\}$ be a consistent sequence of (jointly Borel) probability weights on $\mathbb R^d$ and let $0<p<1$. Let $Y$ be any real response with $(X,Y),(X_1,Y_1),(X_2,Y_2),\dots$ i.i.d., let $L^Y(p\mid X)$ and $U^Y(p\mid X)$ be the lower and upper $p$th quantiles of the conditional distribution of $Y$ given $X$, and let $\hat L_n^Y(p\mid X)$, $\hat U_n^Y(p\mid X)$ be the corresponding quantiles of the weighted empirical distribution $\sum_i W_{ni}(X)\delta_{Y_i}$. Writing $x^-=-(x\wedge0)$ and $x^+=x\vee0$,
--   $$(\hat L_n^Y(p\mid X)-L^Y(p\mid X))^-\to0\quad\text{in probability}\tag{9}$$
--   and
--   $$(\hat U_n^Y(p\mid X)-U^Y(p\mid X))^+\to0\quad\text{in probability}.\tag{10}$$
--   If $r\ge1$ and $E|Y|^r<\infty$, then in (9) and (10) convergence in probability can be replaced by convergence in $L^r$.
--
--   The theorem shows that any weight sequence that consistently estimates conditional means also gives one-sided consistent estimates of conditional quantiles, with no assumption on the distribution of $(X,Y)$. When the conditional quantile is unique ($L=U$) it yields consistency of the midpoint estimate (Corollary 5 of the paper), and it is the input for the consistency in Bayes risk of approximate Bayes rules under piecewise linear loss (Theorem 4, Model 2).
--
--   **Formalization Note.** The response is given by its conditional law given $X$, a Markov kernel $\kappa$, universally quantified; consistency is a hypothesis on the weights alone. $x^-$ and $x^+$ are written $\max(-x,0)$ and $\max(x,0)$. The $L^r$ errors are $[0,\infty]$-valued lower integrals and $E|Y|^r<\infty$ is the finiteness of such an integral. The weight functions are assumed jointly Borel.
-- source:
--   Stone (1977), Ann. Statist. 5, Theorem 3, p. 604 (§7), eqs. (9), (10); proof §12, pp. 616–617

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem 3, p. 604: for a consistent sequence of (measurable) probability weights, `0 < p < 1` and
any conditional law `κ` of `Y` given `X`,
(9) `(L̂ₙ(p|X) − L(p|X))⁻ → 0` and (10) `(Ûₙ(p|X) − U(p|X))⁺ → 0` in probability; if moreover
`r ≥ 1` and `E|Y|ʳ < ∞`, both convergences hold in `Lʳ`. Here `x⁻ = max (−x) 0`, `x⁺ = max x 0`. -/
theorem theorem_3 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W) (hP : StoneRegression.Criterion.ProbWeights W) (hcons : StoneRegression.Criterion.IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    TendstoInMeasure (StoneRegression.Criterion.pairLaw μ κ)
        (fun n ω => max (-(estLowerQ W n p ω - lowerQ κ p (ω 0).1)) 0) atTop (fun _ => 0) ∧
    TendstoInMeasure (StoneRegression.Criterion.pairLaw μ κ)
        (fun n ω => max (estUpperQ W n p ω - upperQ κ p (ω 0).1) 0) atTop (fun _ => 0) ∧
    ∀ r : ℝ, 1 ≤ r → ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞ →
      Tendsto (fun n => ∫⁻ ω, ‖max (-(estLowerQ W n p ω - lowerQ κ p (ω 0).1)) 0‖ₑ ^ r ∂(StoneRegression.Criterion.pairLaw μ κ))
          atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ ω, ‖max (estUpperQ W n p ω - upperQ κ p (ω 0).1) 0‖ₑ ^ r ∂(StoneRegression.Criterion.pairLaw μ κ))
          atTop (𝓝 0) := by sorry

end StoneRegression.Quantile
