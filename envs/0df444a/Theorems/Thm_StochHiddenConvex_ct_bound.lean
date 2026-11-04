-- Prove2me | Theorems.Thm_StochHiddenConvex_ct_bound
-- name    : StochHiddenConvex.ct_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:49.477547+00:00
-- url     : https://prove2.me/theorems/cbb8c514-8dab-4409-937b-03437a57e4dc
-- title:
--   Bound on $C_t$ (p.40, after (28) and (27)) (corrected: assumptions on $\mathbb R^d$)
-- statement:
--   Assume the hypotheses of Theorem 3.2, and in addition that $g$ is differentiable on all of $\mathbb R^d$ with an $S_g$-Lipschitz (diagonal) Jacobian on $\mathbb R^d$. Run MSG with $K\ge1$, $\gamma>0$, $\lambda\ge0$, $x^1\in\mathcal X$, and let $x^*$ minimize $F$ on $\mathcal X$. For every $t\in\{1,\dots,T\}$ the integrand of $C_t$ is integrable and
--   $$C_t\le2L_\phi^2D_{\mathcal X}\gamma\,\frac{KL_f+2L_f}{\mu_g}\Big(1-\frac{\mu_g}{2L_\phi}\Big)^K+4L_\phi^2D_{\mathcal X}^2\gamma\lambda+2L_\phi D_{\mathcal X}\gamma^2S_g\Big(\frac{K^4L_f^2}{8L_\phi^2}+2\lambda^2D_{\mathcal X}^2\Big),$$
--   where $C_t=2\,\mathbb E(u^t-u^*)^\top[g(x^t-\gamma v_F(x^t))-g(x^t)+\gamma\nabla G(u^t)]$ as in (23). Divided by $2\gamma$ and averaged, this gives the last two terms of (10).
--
--   Differences from the source:
--   - correction: Assumption 2.3(a),(c) on 𝒳 (g : 𝒳 → 𝒰) → every gᵢ differentiable on ℝ and the diagonal Jacobian S_g-Lipschitz on ℝ^d (SmoothGlobal); reason: the Taylor step of (29) evaluates g at x^t − γv_F(x^t) ∉ 𝒳, where Assumption 2.3 says nothing; counterexample satisfying every printed assumption (2.1(b), 2.2(c) on ℝ): d = 1, 𝒳 = [0, 1], ξ = ±1 with probability ½, ϕ(x, ξ) = h(x) + ξ with h as in the C_{t,1} example, f the Huber function with f′(y) = max(−1, min(1, y − 1/2)) (L_f = 1), L_ϕ = 2, µ_g = 1, S_g = 10⁻⁶, D_𝒳 = 1, λ = 0, K = 40, γ = 8/K², x¹ = 1, x* = 1/2, t = 1: C_t = 1.02·10⁻⁴, while the printed bound is 2.5·10⁻⁵
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)) and ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
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
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, p.40, display after "Combining with (28) and (27), we have"

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_GlobalModel
import Definitions.Def_StochHiddenConvex_Model_termC

open MeasureTheory

namespace StochHiddenConvex

/-- **The bound on `C_t`.** Chen, He, Hu & Ye, arXiv:2205.01774v3, p.40, display after
"Combining with (28) and (27), we have":
"C_t ≤ 2L_ϕ²D_𝒳γ ((KL_f + 2L_f)/µ_g)(1 − µ_g/(2L_ϕ))^K + 4L_ϕ²D_𝒳²γλ +
2L_ϕD_𝒳γ²S_g(K⁴L_f²/(8L_ϕ²) + 2λ²D_𝒳²)".

At every iteration `t = n + 1` of an MSG run with `γ > 0`, `λ ≥ 0`, `K ≥ 1`, `x¹ ∈ 𝒳` and a
minimizer `x*` of `F` on `𝒳`, under the hypotheses of Theorem 3.2 **and** the smoothness of `g`
on `ℝ^d` (as for (29)); the integrand of `C_t` (27) is integrable. -/
theorem ct_bound {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg) (hsmG : M.SmoothGlobal Sg)
    (K : ℕ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (lam : ℝ) (hlam : 0 ≤ lam)
    (T : ℕ) (x1 : Vec d) (hx1 : x1 ∈ M.box)
    (xstar : Vec d) (hxstar : xstar ∈ M.box) (hmin : ∀ x ∈ M.box, M.F xstar ≤ M.F x)
    (n : Fin T) :
    Integrable (M.integrandC Lphi lam γ K T x1 xstar n) (M.runMeasure K T) ∧
    M.termC Lphi lam γ K T x1 xstar n ≤
      2 * Lphi ^ 2 * D * γ * (((K : ℝ) * Lf + 2 * Lf) / μg) * (1 - μg / (2 * Lphi)) ^ K +
        4 * Lphi ^ 2 * D ^ 2 * γ * lam +
        2 * Lphi * D * γ ^ 2 * Sg * ((K : ℝ) ^ 4 * Lf ^ 2 / (8 * Lphi ^ 2) + 2 * lam ^ 2 * D ^ 2) := by sorry

end StochHiddenConvex
