-- Prove2me | Theorems.Thm_StochHiddenConvex_theorem_3_2
-- name    : StochHiddenConvex.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:44.19352+00:00
-- url     : https://prove2.me/theorems/8c2eb45f-acac-4326-b403-b668a510a931
-- title:
--   Theorem 3.2: explicit global convergence bound (10) for Mirror Stochastic Gradient
-- statement:
--   Consider problem (1), $\min_{x\in\mathcal X}F(x)=\mathbb E[f(\phi(x,\xi))]$ over a box $\mathcal X\subseteq\mathbb R^d$ ($d\ge1$), with separable non-decreasing $\phi$ and convex $f$, and suppose that Assumptions 2.1, 2.2 and 2.3 hold with constants $D_{\mathcal X},L_f,L_\phi,\mu_g,S_g$. Run Mirror Stochastic Gradient (Algorithm 2) for $T\ge1$ iterations with constant stepsize $\gamma_t=\gamma>0$, regularization parameter $\lambda\ge0$, truncation level $K\ge1$ and initialization $x^1\in\mathcal X$, and let $x^*$ be any minimizer of $F$ on $\mathcal X$, $u^1=g(x^1)$, $u^*=g(x^*)$. Then $F(\hat x^T)-F(x^*)$ is integrable and
--   $$\mathbb E[F(\hat x^T)-F(x^*)]\le\frac{\|u^1-u^*\|^2}{2\gamma T}+\gamma\big(L_\phi^2+2L_\phi D_{\mathcal X}S_g\big)\Big(\frac{K^4L_f^2}{16L_\phi^2}+\lambda^2D_{\mathcal X}^2\Big)+2L_\phi^2D_{\mathcal X}^2\lambda+L_\phi^2D_{\mathcal X}\,\frac{KL_f+2L_f}{\mu_g}\Big(1-\frac{\mu_g}{2L_\phi}\Big)^K.\qquad(10)$$
--
--   The four terms are a telescoping term, the variance of $v_F$ and the error of mirroring an SGD step on $G$, the regularization, and the bias of the matrix-inverse estimator. With $\gamma=(D_{\mathcal X}T)^{-1/2}$, small $\lambda$ and $K=\mathcal O(\log\epsilon^{-1})$, the bound gives an $\epsilon$-optimal solution of a nonconvex problem with $\tilde{\mathcal O}(\epsilon^{-2})$ samples, matching the complexity of stochastic convex optimization.
--
--   Differences from the source:
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)) and ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - reading: Assumption 2.2(d): for any ξ ∈ Ξ, ϕ(x, ξ) is differentiable in x almost surely → for every x ∈ 𝒳, for ℙ-almost every ξ, ϕ(·, ξ) is differentiable at x; reason: the use in the proof of Lemma 2.1 (p.30) and in Appendix D.2 (p.44); the other reading follows from 2.2(c) by Rademacher's theorem and makes Theorem 3.2 false (paper.md)
--   - encoding: ϕ a random function; 𝔼ϕ(x, ξ) and 𝔼∇ϕ(x^t, ξ) taken without comment; 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → ϕᵢ jointly measurable, ∂ϕᵢ/∂xᵢ jointly measurable on [X̲ᵢ, X̄ᵢ] × ℝ, ϕᵢ(xᵢ, ·) integrable for x ∈ 𝒳, X̲ᵢ ≤ X̄ᵢ (Regular); reason: the field's standing measurability convention; Algorithm 2 evaluates ∇ϕ at the random iterates x^t ∈ 𝒳, and joint measurability there is what makes its estimators random variables; excludes only data for which the paper's expectations or intervals are undefined
--   - encoding: ∇ϕ(x, ξ) → two-sided derivative of ϕᵢ(·, ξᵢ), with value 0 where it does not exist; reason: by Assumption 2.2(d) the non-differentiable samples are ℙ-null at every x ∈ 𝒳; no expectation changes
--   - encoding: ∇g(x) of g : 𝒳 → 𝒰 → the derivative of gᵢ within [X̲ᵢ, X̄ᵢ] (derivWithin); reason: g is defined on 𝒳; this is the derivative at interior points and the one-sided derivative at faces; together with Assumption 2.3(b) it forces X̲ᵢ < X̄ᵢ, which excludes only degenerate intervals, on which the paper's ∇g is undefined
--   - encoding: ∇ϕ(x, ξ), ∇g(x) and the estimators [∇ĝ(x)]⁻¹ as d × d matrices, with the spectral norm → their diagonal entries carried as vectors; the spectral norm of a diagonal matrix as its largest absolute entry; reason: ϕ is separable, so every matrix involved is diagonal; same values
--   - reading: f is convex, L_f-Lipschitz continuous and continuously differentiable (Assumption 2.2(b)) → on all of ℝ^d; reason: f is a function on ℝ^d and no smaller domain is named
--   - encoding: ℝ^d, i ∈ [d] → 0 < d; reason: the paper's [N] has N ∈ ℕ⁺ (Preliminaries, p.8)
--   - reading: an initialization x¹ → x¹ ∈ 𝒳; reason: x̂^T may equal x¹ and F is defined on 𝒳 (problem (1)); the proof uses ‖u¹ − u*‖ ≤ 2L_ϕD_𝒳
--   - encoding: the random draws of Algorithm 2 (k₁, k₂ uniform on {0, …, K − 1}, k₁ resp. k₂ i.i.d. samples, ξ^t; x̂^T uniform over x¹, …, x^T) → a product probability space: per iteration k₁, k₂ uniform on Fin K, two blocks of K − 1 i.i.d. samples of which the first k₁ resp. k₂ are used, and ξ^t; iterations independent; x̂^T = x^{τ+1} with τ uniform on Fin T and independent; paper index t ↦ t − 1; reason: the same joint law as Algorithm 2
--   - encoding: Π_𝒳(x) := arg min_{y∈𝒳} ‖y − x‖² and Π_𝒰 → coordinatewise clamping to the box; reason: the Euclidean projection onto a box (X̲ᵢ ≤ X̄ᵢ)
--   - encoding: Ŷ(x₁), Ŷ(x₂) defined on a common probability space; ≤_cv the concave order (footnote 1, p.9) → a coupling probability measure on ℝ × ℝ with the two laws as marginals; the published concave order MDPFinance.StructuredModels.LEConcaveOrder; reason: a pair on a common space is the same as its joint law; LEConcaveOrder is the concave order (concave test functions integrable under both laws)
--   - encoding: 𝔼[·] → the conclusion also asserts that each integrand is integrable; reason: rules out Lean's value 0 for a non-integrable integrand; the paper's expectations exist
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Theorem 3.2, p.16 (Eq. (10)); proof Appendix C, pp.38–40

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_iterate

open MeasureTheory

namespace StochHiddenConvex

/-- **Theorem 3.2 (global convergence of Mirror Stochastic Gradient).** Chen, He, Hu & Ye,
arXiv:2205.01774v3, Theorem 3.2, p.16 (proof Appendix C, pp.38–40): "Suppose that Assumptions
2.1, 2.2 and 2.3 hold. For MSG with stepsizes γ_t = γ, and regularization parameter λ ≥ 0, the
expected error of MSG is upper bounded by
𝔼[F(x̂^T) − F(x*)] ≤ ‖u¹ − u*‖²/(2γT) + γ(L_ϕ² + 2L_ϕD_𝒳S_g)(K⁴L_f²/(16L_ϕ²) + λ²D_𝒳²)
+ 2L_ϕ²D_𝒳²λ + L_ϕ²D_𝒳 ((KL_f + 2L_f)/µ_g)(1 − µ_g/(2L_ϕ))^K. (10)"

For every dimension `d`, every model satisfying the standing assumptions of p.1 and Assumptions
2.1–2.3 on `𝒳`, every integer `K ≥ 1`, `γ > 0`, `λ ≥ 0`, `T ≥ 1`, `x¹ ∈ 𝒳` and every minimizer
`x*` of `F` on `𝒳`: the optimality gap of the MSG output is integrable and its expectation
satisfies (10), with `u¹ = g(x¹)` and `u* = g(x*)`.

**Formalization Note.** The run of Algorithm 2 lives on a product probability space
(`outMeasure`): fresh independent randomness `(k₁, k₂, a, b, ξ^t)` at every iteration and an
independent uniform output index. Matrices are diagonal and carried as vectors; `Π_𝒳` is
clamping; `∇g` is the derivative within `𝒳`. -/
theorem theorem_3_2 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg)
    (K : ℕ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (lam : ℝ) (hlam : 0 ≤ lam)
    (T : ℕ) (hT : 1 ≤ T) (x1 : Vec d) (hx1 : x1 ∈ M.box)
    (xstar : Vec d) (hxstar : xstar ∈ M.box) (hmin : ∀ x ∈ M.box, M.F xstar ≤ M.F x) :
    Integrable (fun p => M.F (M.output Lphi lam γ K T x1 p) - M.F xstar) (M.outMeasure K T) ∧
    ∫ p, (M.F (M.output Lphi lam γ K T x1 p) - M.F xstar) ∂(M.outMeasure K T) ≤
      ‖M.g x1 - M.g xstar‖ ^ 2 / (2 * γ * T) +
        γ * (Lphi ^ 2 + 2 * Lphi * D * Sg) *
          ((K : ℝ) ^ 4 * Lf ^ 2 / (16 * Lphi ^ 2) + lam ^ 2 * D ^ 2) +
        2 * Lphi ^ 2 * D ^ 2 * lam +
        Lphi ^ 2 * D * (((K : ℝ) * Lf + 2 * Lf) / μg) * (1 - μg / (2 * Lphi)) ^ K := by sorry

end StochHiddenConvex
