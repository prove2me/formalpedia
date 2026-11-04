-- Prove2me | Theorems.Thm_StochHiddenConvex_eq_24
-- name    : StochHiddenConvex.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:55:41.440766+00:00
-- url     : https://prove2.me/theorems/eab33329-4f2d-4ff0-8f7c-82d251fb8920
-- title:
--   Eq. (24): $\mathbb E(F(\hat x^T)-F(x^*))=\frac1T\sum_t\mathbb E(F(x^t)-F(x^*))=\frac1T\sum_t\mathbb E(G(u^t)-G(u^*))\le\frac1T\sum_t\frac{A_t+B_t+C_t}{2\gamma}$
-- statement:
--   Under the hypotheses of Eq. (23), every expectation below exists and
--   $$\mathbb E(F(\hat x^T)-F(x^*))=\frac1T\sum_{t=1}^T\mathbb E(F(x^t)-F(x^*))=\frac1T\sum_{t=1}^T\mathbb E(G(u^t)-G(u^*))\le\frac1T\sum_{t=1}^T\frac{A_t+B_t+C_t}{2\gamma}.$$
--   The first equality holds because $\hat x^T$ is selected uniformly from $\{x^t\}_{t=1}^T$, the second because $F(x)=G(g(x))$ on $\mathcal X$, and the inequality sums (23).
--
--   The two equalities do not need the conditions on $\mathbb R$ added for (23); the item states all three relations under one set of hypotheses.
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
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (24), p.38

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_GlobalModel
import Definitions.Def_StochHiddenConvex_Model_termC

open MeasureTheory

namespace StochHiddenConvex

/-- **Eq. (24) (averaging).** Chen, He, Hu & Ye, arXiv:2205.01774v3, Eq. (24), p.38:
"𝔼(F(x̂^T) − F(x*)) = (1/T)Σ_{t=1}^T 𝔼(F(x^t) − F(x*)) = (1/T)Σ_{t=1}^T 𝔼(G(u^t) − G(u*))
≤ (1/T)Σ_{t=1}^T (A_t + B_t + C_t)/(2γ)".

All three relations, under the hypotheses of Eq. (23) (`eq_23`), and every expectation involved
exists.

**Formalization Note.** `x̂^T` is `x^{τ+1}` for an index `τ` uniform on `{0, …, T − 1}` and
independent of the run (`outMeasure`); the sums run over `n = t − 1 ∈ Fin T`. The two equalities
hold without the hypotheses on `ℝ` (`MonotoneGlobal`, `IntegrableGlobal`), which only the
inequality uses. -/
theorem eq_24 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi μg Sg : ℝ)
    (hA : M.Assumptions D Lf Lphi μg Sg)
    (hmonoG : M.MonotoneGlobal) (hintG : M.IntegrableGlobal)
    (K : ℕ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (lam : ℝ) (hlam : 0 ≤ lam)
    (T : ℕ) (hT : 1 ≤ T) (x1 : Vec d) (hx1 : x1 ∈ M.box)
    (xstar : Vec d) (hxstar : xstar ∈ M.box) (hmin : ∀ x ∈ M.box, M.F xstar ≤ M.F x) :
    Integrable (fun p => M.F (M.output Lphi lam γ K T x1 p) - M.F xstar) (M.outMeasure K T) ∧
    (∀ n : Fin T, M.StepIntegrable Lphi lam γ K T x1 xstar n) ∧
    ∫ p, (M.F (M.output Lphi lam γ K T x1 p) - M.F xstar) ∂(M.outMeasure K T) =
      1 / (T : ℝ) * ∑ n : Fin T,
        ∫ w, (M.F (M.iterate Lphi lam γ K T x1 n w) - M.F xstar) ∂(M.runMeasure K T) ∧
    1 / (T : ℝ) * ∑ n : Fin T,
        ∫ w, (M.F (M.iterate Lphi lam γ K T x1 n w) - M.F xstar) ∂(M.runMeasure K T) =
      1 / (T : ℝ) * ∑ n : Fin T,
        ∫ w, (M.G (M.g (M.iterate Lphi lam γ K T x1 n w)) - M.G (M.g xstar))
          ∂(M.runMeasure K T) ∧
    1 / (T : ℝ) * ∑ n : Fin T,
        ∫ w, (M.G (M.g (M.iterate Lphi lam γ K T x1 n w)) - M.G (M.g xstar))
          ∂(M.runMeasure K T) ≤
      1 / (T : ℝ) * ∑ n : Fin T,
        (M.termA Lphi lam γ K T x1 xstar n + M.termB Lphi lam γ K T x1 n +
          M.termC Lphi lam γ K T x1 xstar n) / (2 * γ) := by sorry

end StochHiddenConvex
