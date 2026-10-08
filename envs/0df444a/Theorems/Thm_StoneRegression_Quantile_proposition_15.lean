-- Prove2me | Theorems.Thm_StoneRegression_Quantile_proposition_15
-- name    : StoneRegression.Quantile.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:31.268732+00:00
-- url     : https://prove2.me/theorems/60d6cbb8-fbdd-48e8-b9ff-60aeb52204b3
-- title:
--   Proposition 15, p. 617 — E|L̂ₙ|ʳ I{|L̂ₙ| ≥ M} ≤ C/(p ∧ (1 − p)) · E|Y|ʳ I{|Y| ≥ M}, and the same for Ûₙ
-- statement:
--   Fix $n\ge1$. Let $W_n$ be a (jointly Borel) probability weight function satisfying condition (1) with a constant $C\ge1$:
--   $$E\sum_i W_{ni}(X)f(X_i)\le C\,Ef(X)\quad\text{for every nonnegative Borel } f.$$
--   Let $0<p<1$, $M>0$ and $r\ge1$, and let $Y$ be any real response with $(X,Y),(X_1,Y_1),\dots$ i.i.d. Then
--   $$E\,|\hat L_n^Y(p\mid X)|^r\,I_{\{|\hat L_n^Y(p\mid X)|\ge M\}}\le\frac{C}{p\wedge(1-p)}\,E\,|Y|^r I_{\{|Y|\ge M\}},$$
--   and the same inequality holds with $\hat L_n^Y(p\mid X)$ replaced by $\hat U_n^Y(p\mid X)$.
--
--   Since the right side does not depend on $n$ and tends to $0$ as $M\to\infty$ when $E|Y|^r<\infty$, the proposition gives uniform integrability of $|\hat L_n|^r$ and $|\hat U_n|^r$, which turns the convergence in probability of Theorem 3 into convergence in $L^r$.
--
--   **Formalization Note.** The page leaves $r$ unquantified; the Lean statement takes $r\ge1$, the range in which Theorem 3 uses it. Condition (1) is required at the given $n$ only. Expectations are $[0,\infty]$-valued lower integrals. The weight function $W_n$ is assumed jointly Borel.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 15, p. 617 (§12)

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

namespace StoneRegression.Quantile

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 15, p. 617, for one `n ≥ 1`: if `Wₙ` is a (Borel) probability weight function satisfying
(1) at this `n` with constant `C ≥ 1`, then for `0 < p < 1`, `M > 0` and `r ≥ 1`,
`E|L̂ₙ(p|X)|ʳ I{|L̂ₙ(p|X)| ≥ M} ≤ C/(p ∧ (1 − p)) · E|Y|ʳ I{|Y| ≥ M}`, and the same with `Ûₙ(p|X)`.
The page leaves `r` unquantified; `r ≥ 1` is the range Theorem 3 uses. -/
theorem proposition_15 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (n : ℕ) (hn : 1 ≤ n)
    (hWn : Measurable
      (fun q : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => W n q.1 q.2))
    (hPn : ∀ x xs, (∀ i, 0 ≤ W n x xs i) ∧ ∑ i, W n x xs i = 1)
    (C : ℝ≥0) (hC : 1 ≤ C)
    (h1 : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f →
      ∫⁻ ω, ∑ i : Fin n, ‖StoneRegression.Criterion.wAt W n ω i‖ₑ * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(StoneRegression.Criterion.xLaw μ) ≤ C * ∫⁻ x, f x ∂μ)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (M : ℝ) (hM : 0 < M) (r : ℝ) (hr : 1 ≤ r)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    ∫⁻ ω, ‖estLowerQ W n p ω‖ₑ ^ r * (if M ≤ |estLowerQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) ∧
    ∫⁻ ω, ‖estUpperQ W n p ω‖ₑ ^ r * (if M ≤ |estUpperQ W n p ω| then 1 else 0) ∂(StoneRegression.Criterion.pairLaw μ κ) ≤
        ((C : ℝ≥0∞) / ENNReal.ofReal (min p (1 - p))) *
          ∫⁻ q, ‖q.2‖ₑ ^ r * (if M ≤ |q.2| then 1 else 0) ∂(μ ⊗ₘ κ) := by sorry

end StoneRegression.Quantile
