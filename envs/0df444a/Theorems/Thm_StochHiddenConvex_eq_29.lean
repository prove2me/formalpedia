-- Prove2me | Theorems.Thm_StochHiddenConvex_eq_29
-- name    : StochHiddenConvex.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:25.995446+00:00
-- url     : https://prove2.me/theorems/4cda9b19-8f30-462b-a9a7-b9a676e313e5
-- title:
--   Eq. (29): $C_{t,1}\le\frac{\gamma^2S_g}2\mathbb E\|v_F\|^2+\gamma\|\mathbb E[v_G-\nabla g^\top v_F]\|$ (corrected: assumptions on $\mathbb R^d$)
-- statement:
--   Assume the hypotheses of Theorem 3.2, and in addition that $g$ is differentiable on all of $\mathbb R^d$ with an $S_g$-Lipschitz (diagonal) Jacobian on $\mathbb R^d$. For every point $x=x^t\in\mathcal X$ (with $u^t=g(x)$), every integer $K\ge1$, $\gamma>0$ and $\lambda\ge0$, the expectations below exist and
--   $$C_{t,1}=\big\|\mathbb E\big[g(x^t-\gamma v_F(x^t))-u^t+\gamma v_G(u^t)\mid u^t\big]\big\|\le\frac{\gamma^2S_g}{2}\,\mathbb E\big[\|v_F(x^t)\|^2\mid u^t\big]+\gamma\big\|\mathbb E\big[v_G(u^t)-\nabla g(x^t)^\top v_F(x^t)\mid u^t\big]\big\|.$$
--   $C_{t,1}$ measures how far the image $g(x^t-\gamma v_F(x^t))-g(x^t)$ of MSG's step is from the virtual SGD step $-\gamma v_G(u^t)$ in the $u$-space.
--
--   Differences from the source:
--   - correction: Assumption 2.3(a),(c) on 𝒳 (g : 𝒳 → 𝒰) → every gᵢ differentiable on ℝ and the diagonal Jacobian S_g-Lipschitz on ℝ^d (SmoothGlobal); reason: the Taylor step of (29) evaluates g at x^t − γv_F(x^t) ∉ 𝒳, where Assumption 2.3 says nothing; counterexample satisfying every printed assumption (2.1(b), 2.2(c) on ℝ): d = 1, 𝒳 = [0, 1], ξ ≡ 0, ϕ(x) = x for x ≤ 1, x + (x − 1)² on [1, 3/2], 2x − 5/4 beyond (L_ϕ = 2, µ_g = 1, S_g = 10⁻⁶ on 𝒳), f(y) = −y, λ = 0, x^t = 1, K = 40, γ = 8/K²: C_{t,1} = 8.16·10⁻⁴, while the right side of (29) is 5.1·10⁻⁸ and the printed C_{t,1} bound is 3.0·10⁻⁶
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
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (29), p.39

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_GlobalModel
import Definitions.Def_StochHiddenConvex_Model_iterate

open MeasureTheory

namespace StochHiddenConvex

/-- **Eq. (29) (splitting `C_{t,1}`).** Chen, He, Hu & Ye, arXiv:2205.01774v3, Eq. (29), p.39:
"C_{t,1} = ‖𝔼[g(x^t − γv_F(x^t)) − u^t + γv_G(u^t) | u^t]‖ ≤ … ≤
(γ²S_g/2)𝔼[‖v_F(x^t)‖² | u^t] + γ‖𝔼[v_G(u^t) − ∇g(x^t)ᵀv_F(x^t) | u^t]‖".

The final inequality, at every point `x = x^t ∈ 𝒳` (`u^t = g(x)`), for every `γ > 0`, `λ ≥ 0`,
`K ≥ 1`, under the hypotheses of Theorem 3.2 **and** the smoothness of `g` on all of `ℝ^d`; every
expectation involved exists.

**Formalization Note.** Corrected: the Taylor bound uses "the Lipschitz continuity of ∇g" (p.40)
at `x^t − γ v_F(x^t) ∉ 𝒳`, where Assumption 2.3 (stated for `g : 𝒳 → 𝒰`) says nothing; with 2.3
on `𝒳` only the display fails (counterexample in the item's statement). `SmoothGlobal` puts
2.3(a),(c) on `ℝ^d`. Conditioning on `u^t` is integration over the fresh randomness at `x`. -/
theorem eq_29 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg) (hsmG : M.SmoothGlobal Sg)
    (K : ℕ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : Vec d) (hx : x ∈ M.box) :
    Integrable (fun ω => M.g (x - γ • M.vF Lphi lam K x ω) - M.g x + γ • M.vG Lphi K x ω)
      (M.iterMeasure K) ∧
    Integrable (fun ω => ‖M.vF Lphi lam K x ω‖ ^ 2) (M.iterMeasure K) ∧
    Integrable (fun ω => M.vG Lphi K x ω - M.gJacT x (M.vF Lphi lam K x ω)) (M.iterMeasure K) ∧
    ‖∫ ω, (M.g (x - γ • M.vF Lphi lam K x ω) - M.g x + γ • M.vG Lphi K x ω)
        ∂(M.iterMeasure K)‖ ≤
      γ ^ 2 * Sg / 2 * ∫ ω, ‖M.vF Lphi lam K x ω‖ ^ 2 ∂(M.iterMeasure K) +
        γ * ‖∫ ω, (M.vG Lphi K x ω - M.gJacT x (M.vF Lphi lam K x ω)) ∂(M.iterMeasure K)‖ := by sorry

end StochHiddenConvex
