-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_regression_limit
-- name    : ShapeSOS.ConvexConsistency.regression_limit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:24:19.21801+00:00
-- url     : https://prove2.me/theorems/23f56921-6a4c-4b37-b572-113417b65bb6
-- title:
--   Proposition 3.12 — both printed fixed-degree regression limits
-- statement:
--   Let $C$ be a closed subset of a full-dimensional real box $B\subset\mathbb R^n$, with nonempty interior and no point on $\partial B$. Fix $d\in\mathbb N$ and assume Assumptions 1–3. Both assertions hold:
--
--   1. For a twice continuously differentiable convex $f$, let $g_d$ be any best uniform convex polynomial approximant of degree at most $d$, and let $\bar g_{m,d}$ be actual empirical minimizers from (9). Then
--   $$\sup_{x\in C}|\bar g_{m,d}(x)-g_d(x)|\longrightarrow0\quad\text{almost surely as }m\to\infty.$$
--   2. For a continuously differentiable $f$ with one-sided $K$-bounded derivatives, let $h_d$ be a best uniform bounded-derivative approximant and let $\bar h_{m,d}$ minimize exactly the printed (10), whose derivative constraints are on $f$. Then
--   $$\sup_{x\in C}|\bar h_{m,d}(x)-h_d(x)|\longrightarrow0\quad\text{almost surely as }m\to\infty.$$
--   The uniform approximants and empirical minimizers solve different problems. Their printed limiting identification is retained, with the counterexample in I2.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: smoothness on a closed box → ContDiffOn and coordinate fderivWithin on that box; reason: within-domain derivatives preserve the interior derivatives and their continuous boundary values
--   - encoding: Assumptions 1–3 on samples and conditional noise laws → one probability space with an infinite measurable stream, conditional-expectation factorization on every measurable rectangle, and explicit integrability; reason: finite prefixes recover the displayed laws; finite second moments imply the added integrability clauses
--   - reading: full-dimensional interior regions and positive probability on full-dimensional subsets → full-dimensional means nonempty Euclidean interior; probability assertions concern measurable subsets; reason: this is the support interpretation; full affine hull alone would incorrectly force mass on finite affine bases
--   - encoding: named minimizers of the displayed problems → concrete feasible sets, losses, and attained-minimum relations; reason: optimality compares against every feasible polynomial; it is never replaced by a desired asymptotic property
--   - generalization: named empirical minimizing sequences → arbitrary sequences that are actual minimizers on an almost-sure eventual tail; reason: the source sequences specialize to these; finite initial prefixes do not change any limit
--   - generalization: Proposition 3.11 describes a smooth function on real n-space → only the required C¹ or C² regularity within the box is imposed; reason: globally smooth source functions specialize to this box-local statement, with the same values and interior derivatives
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 14, Proposition 3.12

import Definitions.Def_ShapeSOS_ConvexConsistency_Sampling

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem regression_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (B : Box n) (C : Set (Vec n)) (hC : InteriorRegion B C)
    (f : Vec n → ℝ) (X : ℕ → Ω → Vec n) (ν : ℕ → Ω → ℝ)
    (hs : SamplingAssumptions μ B f X ν) (d : ℕ) :
    (ContDiffOn ℝ 2 f B.carrier → ConvexOn ℝ B.carrier f →
      ∀ gd : Poly n, Minimizes (convexClass B d) (approximationLoss B f) gd →
      ∀ gbar : ℕ → Ω → Poly n,
        (∀ᵐ ω ∂μ, ∀ᶠ m in atTop, Minimizes (convexClass B d)
          (empiricalLoss m (fun i => X i ω) (fun i => response f X ν i ω)) (gbar m ω)) →
        ∀ᵐ ω ∂μ, Tendsto (fun m => uniformError C (value (gbar m ω)) (value gd))
          atTop (𝓝 0)) ∧
    (∀ K : DerivativeBounds n, K.oneSided → HasBoundedDerivatives B K f →
      ∀ hd : Poly n, Minimizes (derivativeClass B K d) (approximationLoss B f) hd →
      ∀ hbar : ℕ → Ω → Poly n,
        (∀ᵐ ω ∂μ, ∀ᶠ m in atTop, Minimizes (printedDerivativeClass B K f d)
          (empiricalLoss m (fun i => X i ω) (fun i => response f X ν i ω)) (hbar m ω)) →
        ∀ᵐ ω ∂μ, Tendsto (fun m => uniformError C (value (hbar m ω)) (value hd))
          atTop (𝓝 0)) := by sorry

end ShapeSOS.ConvexConsistency
