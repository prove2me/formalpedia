-- Prove2me | Theorems.Thm_StochHiddenConvex_ct1_bound
-- name    : StochHiddenConvex.ct1_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:53.865765+00:00
-- url     : https://prove2.me/theorems/01557943-7bfe-4250-86d9-1d877b51f88a
-- title:
--   Bound on $C_{t,1}$ (p.40, after (31)) (corrected: assumptions on $\mathbb R^d$)
-- statement:
--   Assume the hypotheses of Theorem 3.2, and in addition that $g$ is differentiable on all of $\mathbb R^d$ with an $S_g$-Lipschitz (diagonal) Jacobian on $\mathbb R^d$. For every point $x=x^t\in\mathcal X$, every integer $K\ge1$, $\gamma>0$ and $\lambda\ge0$, the integrand is integrable and
--   $$C_{t,1}\le\gamma\,\frac{L_\phi KL_f}{2\mu_g}\Big(1-\frac{\mu_g}{2L_\phi}\Big)^K+\gamma L_\phi\lambda D_{\mathcal X}+\frac{\gamma^2S_g}{2}\Big(\frac{K^4L_f^2}{8L_\phi^2}+2\lambda^2D_{\mathcal X}^2\Big),$$
--   where $C_{t,1}=\|\mathbb E[g(x^t-\gamma v_F(x^t))-u^t+\gamma v_G(u^t)\mid u^t]\|$. It combines (29), (30) and (31).
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
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, p.40, display after "Plugging (30), (31) into (29), we have"

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_GlobalModel
import Definitions.Def_StochHiddenConvex_Model_iterate

open MeasureTheory

namespace StochHiddenConvex

/-- **The bound on `C_{t,1}`.** Chen, He, Hu & Ye, arXiv:2205.01774v3, p.40, display after
"Plugging (30), (31) into (29), we have":
"C_{t,1} ≤ γ (L_ϕKL_f/(2µ_g))(1 − µ_g/(2L_ϕ))^K + γL_ϕλD_𝒳 + (γ²S_g/2)(K⁴L_f²/(8L_ϕ²) + 2λ²D_𝒳²)".

At every point `x = x^t ∈ 𝒳` (`u^t = g(x)`), for every `γ > 0`, `λ ≥ 0`, `K ≥ 1`, under the
hypotheses of Theorem 3.2 **and** the smoothness of `g` on `ℝ^d` (as for (29)).

**Formalization Note.** `C_{t,1} = ‖𝔼[g(x^t − γv_F(x^t)) − u^t + γv_G(u^t) | u^t]‖`, with the
conditional expectation computed over the fresh randomness at `x`. -/
theorem ct1_bound {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg) (hsmG : M.SmoothGlobal Sg)
    (K : ℕ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : Vec d) (hx : x ∈ M.box) :
    Integrable (fun ω => M.g (x - γ • M.vF Lphi lam K x ω) - M.g x + γ • M.vG Lphi K x ω)
      (M.iterMeasure K) ∧
    ‖∫ ω, (M.g (x - γ • M.vF Lphi lam K x ω) - M.g x + γ • M.vG Lphi K x ω)
        ∂(M.iterMeasure K)‖ ≤
      γ * (Lphi * K * Lf / (2 * μg)) * (1 - μg / (2 * Lphi)) ^ K + γ * Lphi * lam * D +
        γ ^ 2 * Sg / 2 * ((K : ℝ) ^ 4 * Lf ^ 2 / (8 * Lphi ^ 2) + 2 * lam ^ 2 * D ^ 2) := by sorry

end StochHiddenConvex
