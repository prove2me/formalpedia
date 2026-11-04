-- Prove2me | Theorems.Thm_StochHiddenConvex_eq_28
-- name    : StochHiddenConvex.eq_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:17.319131+00:00
-- url     : https://prove2.me/theorems/ad05fafa-8662-43d5-962f-e6d848a284f6
-- title:
--   Eq. (28): $C_{t,2}=\|\mathbb E[\nabla G(u^t)-v_G(u^t)\mid x^t]\|\le\frac1{\mu_g}(1-\frac{\mu_g}{2L_\phi})^KL_\phi L_f$
-- statement:
--   Under the hypotheses of Theorem 3.2, for every point $x=x^t\in\mathcal X$ (with $u^t=g(x)$) and every integer $K\ge1$, $v_G$ is integrable and
--   $$C_{t,2}=\big\|\mathbb E[\nabla G(u^t)-v_G(u^t)\mid x^t]\big\|\le\frac1{\mu_g}\Big(1-\frac{\mu_g}{2L_\phi}\Big)^KL_\phi L_f.$$
--   $C_{t,2}$ is the bias of the $u$-space gradient estimator $v_G$; it is controlled by the bias of the Neumann-series estimator (Lemma 2.2) and $\|\nabla F(x)\|\le L_\phi L_f$.
--
--   Differences from the source:
--   - encoding: 𝔼[· | x^t] and 𝔼[· | u^t] → the integral over one iteration's fresh randomness at a fixed point x ∈ 𝒳 (with u^t = g(x)); reason: the fresh randomness is independent of x^t, so the conditional expectation at x^t = x is this integral; u^t determines x^t on 𝒳 by Assumption 2.3(b)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)) and ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
--   - reading: Assumption 2.2(d): for any ξ ∈ Ξ, ϕ(x, ξ) is differentiable in x almost surely → for every x ∈ 𝒳, for ℙ-almost every ξ, ϕ(·, ξ) is differentiable at x; reason: the use in the proof of Lemma 2.1 (p.30) and in Appendix D.2 (p.44); the other reading follows from 2.2(c) by Rademacher's theorem and makes Theorem 3.2 false (paper.md)
--   - encoding: ϕ a random function; 𝔼ϕ(x, ξ) and 𝔼∇ϕ(x^t, ξ) taken without comment; 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → ϕᵢ jointly measurable, ∂ϕᵢ/∂xᵢ jointly measurable on [X̲ᵢ, X̄ᵢ] × ℝ, ϕᵢ(xᵢ, ·) integrable for x ∈ 𝒳, X̲ᵢ ≤ X̄ᵢ (Regular); reason: the field's standing measurability convention; Algorithm 2 evaluates ∇ϕ at the random iterates x^t ∈ 𝒳, and joint measurability there is what makes its estimators random variables; excludes only data for which the paper's expectations or intervals are undefined
--   - encoding: ∇ϕ(x, ξ) → two-sided derivative of ϕᵢ(·, ξᵢ), with value 0 where it does not exist; reason: by Assumption 2.2(d) the non-differentiable samples are ℙ-null at every x ∈ 𝒳; no expectation changes
--   - encoding: ∇g(x) of g : 𝒳 → 𝒰 → the derivative of gᵢ within [X̲ᵢ, X̄ᵢ] (derivWithin); reason: g is defined on 𝒳; this is the derivative at interior points and the one-sided derivative at faces; together with Assumption 2.3(b) it forces X̲ᵢ < X̄ᵢ, which excludes only degenerate intervals, on which the paper's ∇g is undefined
--   - encoding: ∇ϕ(x, ξ), ∇g(x) and the estimators [∇ĝ(x)]⁻¹ as d × d matrices, with the spectral norm → their diagonal entries carried as vectors; the spectral norm of a diagonal matrix as its largest absolute entry; reason: ϕ is separable, so every matrix involved is diagonal; same values
--   - reading: f is convex, L_f-Lipschitz continuous and continuously differentiable (Assumption 2.2(b)) → on all of ℝ^d; reason: f is a function on ℝ^d and no smaller domain is named
--   - encoding: ℝ^d, i ∈ [d] → 0 < d; reason: the paper's [N] has N ∈ ℕ⁺ (Preliminaries, p.8)
--   - encoding: Ŷ(x₁), Ŷ(x₂) defined on a common probability space; ≤_cv the concave order (footnote 1, p.9) → a coupling probability measure on ℝ × ℝ with the two laws as marginals; the published concave order MDPFinance.StructuredModels.LEConcaveOrder; reason: a pair on a common space is the same as its joint law; LEConcaveOrder is the concave order (concave test functions integrable under both laws)
--   - encoding: 𝔼[·] → the conclusion also asserts that each integrand is integrable; reason: rules out Lean's value 0 for a non-integrable integrand; the paper's expectations exist
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (28), p.39

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_iterate

open MeasureTheory

namespace StochHiddenConvex

/-- **Eq. (28) (bias of `v_G`, the term `C_{t,2}`).** Chen, He, Hu & Ye, arXiv:2205.01774v3,
Eq. (28), p.39: "C_{t,2} = ‖𝔼[∇G(u^t) − v_G(u^t) | x^t]‖ = … ≤ (1/µ_g)(1 − µ_g/(2L_ϕ))^K L_ϕL_f".

The outer inequality, at every point `x = x^t ∈ 𝒳` (with `u^t = g(x)`), under the hypotheses of
Theorem 3.2, for every integer `K ≥ 1`; `v_G` is integrable.

**Formalization Note.** Conditioning on `x^t` is integration over one iteration's fresh
randomness at the fixed point `x` (`iterMeasure`); the two agree because that randomness is
independent of `x^t`. `∇G(u^t)` is `gradG (g x)`. -/
theorem eq_28 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg) (K : ℕ) (hK : 1 ≤ K) (x : Vec d) (hx : x ∈ M.box) :
    Integrable (fun ω => M.vG Lphi K x ω) (M.iterMeasure K) ∧
    ‖M.gradG (M.g x) - ∫ ω, M.vG Lphi K x ω ∂(M.iterMeasure K)‖ ≤
      1 / μg * (1 - μg / (2 * Lphi)) ^ K * Lphi * Lf := by sorry

end StochHiddenConvex
