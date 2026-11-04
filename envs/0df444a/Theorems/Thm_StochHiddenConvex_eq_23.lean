-- Prove2me | Theorems.Thm_StochHiddenConvex_eq_23
-- name    : StochHiddenConvex.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:03.136343+00:00
-- url     : https://prove2.me/theorems/d4780531-e7b2-4bb7-96a2-c344e0103042
-- title:
--   Eq. (23): the one-step inequality $2\gamma\,\mathbb E(G(u^t)-G(u^*))\le A_t+B_t+C_t$
-- statement:
--   Assume the hypotheses of Theorem 3.2, and in addition that every $\phi_i(\cdot,\xi_i)$ is non-decreasing on all of $\mathbb R$ and $g$ is finite on $\mathbb R^d$. Run MSG with $K\ge1$, stepsize $\gamma>0$, $\lambda\ge0$, $x^1\in\mathcal X$, and let $x^*$ minimize $F$ on $\mathcal X$, $u^t=g(x^t)$, $u^*=g(x^*)$. Then for every $t\in\{1,\dots,T\}$ all expectations below exist and
--   $$2\gamma\big(\mathbb E(G(u^t)-G(u^*))\big)\le\underbrace{\mathbb E\|u^t-u^*\|^2-\mathbb E\|u^{t+1}-u^*\|^2}_{A_t}+\underbrace{\mathbb E\big[\|g(x^t-\gamma v_F(x^t))-g(x^t)\|^2\big]}_{B_t}+\underbrace{2\,\mathbb E(u^t-u^*)^\top\big[g(x^t-\gamma v_F(x^t))-g(x^t)+\gamma\nabla G(u^t)\big]}_{C_t}.$$
--
--   This is the projected-SGD potential inequality carried out in the $u$-space, which MSG never visits: the error splits into a telescoping term, a variance term and a bias/curvature term.
--
--   Differences from the source:
--   - reading: Assumption 2.1(b), stated without a domain for x → ϕᵢ(·, ξᵢ) non-decreasing on all of ℝ (MonotoneGlobal); reason: the proof applies Lemma 3.1 outside 𝒳 (Cases II–III, p.32, used at x^t − γv_F(x^t), p.38)
--   - encoding: g(x) = 𝔼ϕ(x, ξ) at points x ∉ 𝒳 → ϕᵢ(xᵢ, ·) integrable at every x ∈ ℝ^d (IntegrableGlobal); reason: the paper evaluates g there; excludes only data for which it is undefined
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - generalization: ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
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
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (23), p.38

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_GlobalModel
import Definitions.Def_StochHiddenConvex_Model_termC

open MeasureTheory

namespace StochHiddenConvex

/-- **Eq. (23) (one-step inequality of MSG).** Chen, He, Hu & Ye, arXiv:2205.01774v3, Eq. (23),
p.38: "2γ(𝔼(G(u^t) − G(u*)) ≤ 𝔼‖u^t − u*‖² − 𝔼‖u^{t+1} − u*‖² + 𝔼[‖g(x^t − γv_F(x^t)) − g(x^t)‖²]
+ 2𝔼(u^t − u*)ᵀ[g(x^t − γv_F(x^t)) − g(x^t) + γ∇G(u^t)]", with the three terms `A_t`, `B_t`,
`C_t`.

Under the hypotheses of Theorem 3.2, for every iteration `t = n + 1 ∈ {1, …, T}` of MSG with
stepsize `γ > 0`, `λ ≥ 0`, `K ≥ 1`, `x¹ ∈ 𝒳` and a minimizer `x*` of `F` on `𝒳`; every expectation
involved exists.

**Formalization Note.** Step (b) applies Lemma 3.1 at `x^t − γ v_F(x^t) ∉ 𝒳`, so Assumption
2.1(b) is used on all of `ℝ` (`MonotoneGlobal`) and `g = 𝔼ϕ` is defined there
(`IntegrableGlobal`). `∇G(u^t)` is `gradG (g x^t)` (Lemma 2.1). -/
theorem eq_23 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg)
    (hmonoG : M.MonotoneGlobal) (hintG : M.IntegrableGlobal)
    (K : ℕ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (lam : ℝ) (hlam : 0 ≤ lam)
    (T : ℕ) (x1 : Vec d) (hx1 : x1 ∈ M.box)
    (xstar : Vec d) (hxstar : xstar ∈ M.box) (hmin : ∀ x ∈ M.box, M.F xstar ≤ M.F x)
    (n : Fin T) :
    M.StepIntegrable Lphi lam γ K T x1 xstar n ∧
    2 * γ * (∫ w, (M.G (M.g (M.iterate Lphi lam γ K T x1 n w)) - M.G (M.g xstar))
        ∂(M.runMeasure K T)) ≤
      M.termA Lphi lam γ K T x1 xstar n + M.termB Lphi lam γ K T x1 n +
        M.termC Lphi lam γ K T x1 xstar n := by sorry

end StochHiddenConvex
