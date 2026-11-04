-- Prove2me | Theorems.Thm_StochHiddenConvex_lemma_2_1
-- name    : StochHiddenConvex.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:20.772197+00:00
-- url     : https://prove2.me/theorems/05b75354-1dd1-42a0-877c-8949a690e08c
-- title:
--   Lemma 2.1: gradient formulas (4) for $\nabla F$ and (5) for $\nabla G$
-- statement:
--   Under Assumptions 2.2(b)(c)(d) and 2.3(a)(b) (and the standing monotonicity of $\phi$), for any $x\in\mathcal X$ and any $u\in\mathcal U$,
--   $$\nabla F(x)=\mathbb E_\xi\big[\nabla\phi(x,\xi)^\top\nabla f(\phi(x,\xi))\big],\qquad(4)$$
--   $$\nabla G(u)=[\nabla g(g^{-1}(u))]^{-\top}\,\mathbb E_\xi\big[\nabla\phi(g^{-1}(u),\xi)^\top\nabla f(\phi(g^{-1}(u),\xi))\big].\qquad(5)$$
--   Here $\nabla F(x)$ is the gradient of $F$ within $\mathcal X$ and $\nabla G(u)$ the gradient of $G$ within $\mathcal U$.
--
--   Formula (4) is what the sample $\nabla\phi(x^t,\xi^t)^\top\nabla f(\phi(x^t,\xi^t))$ estimates, and (5) is the gradient of the convex reformulation that MSG mirrors.
--
--   Differences from the source:
--   - encoding: ∇F(x) and ∇G(u) at x ∈ 𝒳 and u ∈ 𝒰 → gradients within 𝒳 and within 𝒰 (HasGradientWithinAt); reason: F and G are objectives on 𝒳 and 𝒰; these are the gradients at interior points and the one-sided ones at faces
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)) and ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - reading: Assumption 2.2(d): for any ξ ∈ Ξ, ϕ(x, ξ) is differentiable in x almost surely → for every x ∈ 𝒳, for ℙ-almost every ξ, ϕ(·, ξ) is differentiable at x; reason: the use in the proof of Lemma 2.1 (p.30) and in Appendix D.2 (p.44); the other reading follows from 2.2(c) by Rademacher's theorem and makes Theorem 3.2 false (paper.md)
--   - encoding: ϕ a random function; 𝔼ϕ(x, ξ) and 𝔼∇ϕ(x, ξ) taken without comment; 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → ϕᵢ jointly measurable, ϕᵢ(xᵢ, ·) integrable for x ∈ 𝒳, X̲ᵢ ≤ X̄ᵢ (RegularData); reason: the field's standing measurability convention; excludes only data for which the paper's expectations or intervals are undefined
--   - encoding: ∇ϕ(x, ξ) → two-sided derivative of ϕᵢ(·, ξᵢ), with value 0 where it does not exist; reason: by Assumption 2.2(d) the non-differentiable samples are ℙ-null at every x ∈ 𝒳; no expectation changes
--   - encoding: ∇g(x) of g : 𝒳 → 𝒰 → the derivative of gᵢ within [X̲ᵢ, X̄ᵢ] (derivWithin); reason: g is defined on 𝒳; this is the derivative at interior points and the one-sided derivative at faces; together with Assumption 2.3(b) it forces X̲ᵢ < X̄ᵢ, which excludes only degenerate intervals, on which the paper's ∇g is undefined
--   - encoding: ∇ϕ(x, ξ), ∇g(x) and the estimators [∇ĝ(x)]⁻¹ as d × d matrices, with the spectral norm → their diagonal entries carried as vectors; the spectral norm of a diagonal matrix as its largest absolute entry; reason: ϕ is separable, so every matrix involved is diagonal; same values
--   - reading: f is convex, L_f-Lipschitz continuous and continuously differentiable (Assumption 2.2(b)) → on all of ℝ^d; reason: f is a function on ℝ^d and no smaller domain is named
--   - reading: Assumptions 2.2(b)(c)(d) and 2.3(a)(b) → plus the standing monotonicity of ϕ on 𝒳 (p.1); reason: the paper assumes it throughout (p.1, "Throughout the paper")
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Lemma 2.1, p.10; proof Appendix A.1, pp.29–30

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions

open MeasureTheory

namespace StochHiddenConvex

/-- **Lemma 2.1 (gradient formulas).** Chen, He, Hu & Ye, arXiv:2205.01774v3, Lemma 2.1, p.10
(proof Appendix A.1, pp.29–30): "Under Assumptions 2.2(b)(c)(d) and 2.3(a)(b), for any x ∈ 𝒳 and
any u ∈ 𝒰, we have ∇F(x) = 𝔼_ξ[∇ϕ(x, ξ)ᵀ∇f(ϕ(x, ξ))] (4),
∇G(u) = [∇g(g⁻¹(u))]^{−⊤}𝔼_ξ[∇ϕ(g⁻¹(u), ξ)ᵀ∇f(ϕ(g⁻¹(u), ξ))] (5)."

**Formalization Note.** `∇F(x)` and `∇G(u)` are gradients within `𝒳` and `𝒰`
(`HasGradientWithinAt`), one-sided at faces. The standing monotonicity of p.1 is included. -/
theorem lemma_2_1 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (Lf Lphi μg : ℝ)
    (hreg : M.RegularData) (h21b : M.MonotoneOnBox)
    (h22b : M.Assumption22b Lf) (h22c : M.Assumption22c Lphi) (h22d : M.Assumption22d)
    (h23a : M.Assumption23a) (h23b : M.Assumption23b μg) :
    (∀ x ∈ M.box, HasGradientWithinAt M.F (M.gradF x) M.box x) ∧
    (∀ u ∈ M.Ubox, HasGradientWithinAt M.G (M.gradG u) M.Ubox u) := by sorry

end StochHiddenConvex
