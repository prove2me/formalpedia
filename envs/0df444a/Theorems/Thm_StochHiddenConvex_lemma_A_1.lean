-- Prove2me | Theorems.Thm_StochHiddenConvex_lemma_A_1
-- name    : StochHiddenConvex.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:24.841916+00:00
-- url     : https://prove2.me/theorems/b96ef582-eb1c-4f76-92ac-71d3d371c20f
-- title:
--   Lemma A.1: $\mathbb E\|v_G\|^2\le\frac{K^2L_f^2}4$ and $\mathbb E\|v_F\|^2\le\frac{K^4L_f^2}{8L_\phi^2}+2\lambda^2D_{\mathcal X}^2$
-- statement:
--   Under Assumption 2.2 (with the standing monotonicity of $\phi$), for every $x\in\mathcal X$ (with $u=g(x)$), every integer $K\ge1$ and every $\lambda$, the estimators $v_G$ and $v_F$ of one MSG iteration at $x$ satisfy
--   $$\mathbb E\|v_G(u)\|^2\le\frac{K^2L_f^2}{4},\qquad\mathbb E\|v_F(x)\|^2\le\frac{K^4L_f^2}{8L_\phi^2}+2\lambda^2D_{\mathcal X}^2,$$
--   and both expectations exist. These are the variance bounds that enter $B_t$ (26) and the curvature term of $C_{t,1}$ (30).
--
--   Differences from the source:
--   - reading: 𝔼‖v_G(x)‖² and 𝔼‖v_F(u)‖² → v_G at u = g(x) and v_F at x (both as functions of x); reason: the printed arguments are swapped (slip); the proof on p.33 uses v_G(u), v_F(x)
--   - reading: 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → either X̲ᵢ < X̄ᵢ for every i, or ϕᵢ(·, ξᵢ) non-decreasing and ϕ(·, ξ) L_ϕ-Lipschitz on all of ℝ^d (MonotoneGlobal and LipschitzGlobal); reason: with monotonicity and Assumption 2.2(c) read on 𝒳, ∇ϕ at a point of a degenerate interval is unconstrained and the bounds fail there; under the ℝ^d reading (the second alternative) the box may be degenerate, so the statement specializes to the source on either reading
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)) and ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - reading: Assumption 2.2(d): for any ξ ∈ Ξ, ϕ(x, ξ) is differentiable in x almost surely → for every x ∈ 𝒳, for ℙ-almost every ξ, ϕ(·, ξ) is differentiable at x; reason: the use in the proof of Lemma 2.1 (p.30) and in Appendix D.2 (p.44); the other reading follows from 2.2(c) by Rademacher's theorem and makes Theorem 3.2 false (paper.md)
--   - encoding: ϕ a random function; 𝔼ϕ(x, ξ) and 𝔼∇ϕ(x, ξ) taken without comment; 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → ϕᵢ jointly measurable, ϕᵢ(xᵢ, ·) integrable for x ∈ 𝒳, X̲ᵢ ≤ X̄ᵢ (RegularData); reason: the field's standing measurability convention; excludes only data for which the paper's expectations or intervals are undefined
--   - encoding: ∇ϕ(x, ξ) → two-sided derivative of ϕᵢ(·, ξᵢ), with value 0 where it does not exist; reason: by Assumption 2.2(d) the non-differentiable samples are ℙ-null at every x ∈ 𝒳; no expectation changes
--   - encoding: ∇ϕ(x, ξ), ∇g(x) and the estimators [∇ĝ(x)]⁻¹ as d × d matrices, with the spectral norm → their diagonal entries carried as vectors; the spectral norm of a diagonal matrix as its largest absolute entry; reason: ϕ is separable, so every matrix involved is diagonal; same values
--   - reading: f is convex, L_f-Lipschitz continuous and continuously differentiable (Assumption 2.2(b)) → on all of ℝ^d; reason: f is a function on ℝ^d and no smaller domain is named
--   - encoding: the random draws of Algorithm 2 (k₁, k₂ uniform on {0, …, K − 1}, k₁ resp. k₂ i.i.d. samples, ξ^t; x̂^T uniform over x¹, …, x^T) → a product probability space: per iteration k₁, k₂ uniform on Fin K, two blocks of K − 1 i.i.d. samples of which the first k₁ resp. k₂ are used, and ξ^t; iterations independent; x̂^T = x^{τ+1} with τ uniform on Fin T and independent; paper index t ↦ t − 1; reason: the same joint law as Algorithm 2
--   - encoding: 𝔼[·] → the conclusion also asserts that each integrand is integrable; reason: rules out Lean's value 0 for a non-integrable integrand; the paper's expectations exist
--   - reading: Assumption 2.2 → plus the standing monotonicity of ϕ on 𝒳 (p.1); reason: assumed throughout the paper (p.1); used through Lemma 2.2's second-moment bound
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Lemma A.1, p.33

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_iterate
import Definitions.Def_StochHiddenConvex_Model_GlobalModel

open MeasureTheory

namespace StochHiddenConvex

/-- **Lemma A.1 (second moments of `v_G` and `v_F`).** Chen, He, Hu & Ye, arXiv:2205.01774v3,
Lemma A.1, p.33: "Under Assumption 2.2, the second moment of v_G(u) and v_F(x) are bounded with
𝔼‖v_G(x)‖² ≤ K²L_f²/4. 𝔼‖v_F(u)‖² ≤ K⁴L_f²/(8L_ϕ²) + 2λ²D_𝒳²."

At every `x ∈ 𝒳` (with `u = g(x)`), for every integer `K ≥ 1` and every `λ`, the expectation being
over one iteration's randomness of Algorithm 2.

**Formalization Note.** The printed arguments `v_G(x)`, `v_F(u)` are swapped (slip); `vG` is a
function of `x`. Either the intervals `[X̲ᵢ, X̄ᵢ]` are nondegenerate, as `∇ϕ` on `𝒳` requires when
the monotonicity and Assumption 2.2(c) are read on `𝒳`, or both hold on all of `ℝ^d` (the reading
without a domain), in which case the box may be degenerate. The standing monotonicity of p.1 is included (used through
Lemma 2.2's `0 ⪯ ∇ϕ`). -/
theorem lemma_A_1 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (D Lf Lphi : ℝ)
    (hreg : M.RegularData) (h21b : M.MonotoneOnBox)
    (h22a : M.Assumption22a D) (h22b : M.Assumption22b Lf) (h22c : M.Assumption22c Lphi)
    (h22d : M.Assumption22d)
    (hnd : (∀ i, M.lo i < M.hi i) ∨ (M.MonotoneGlobal ∧ M.LipschitzGlobal Lphi))
    (K : ℕ) (hK : 1 ≤ K) (lam : ℝ) (x : Vec d) (hx : x ∈ M.box) :
    Integrable (fun ω => ‖M.vG Lphi K x ω‖ ^ 2) (M.iterMeasure K) ∧
    ∫ ω, ‖M.vG Lphi K x ω‖ ^ 2 ∂(M.iterMeasure K) ≤ (K : ℝ) ^ 2 * Lf ^ 2 / 4 ∧
    Integrable (fun ω => ‖M.vF Lphi lam K x ω‖ ^ 2) (M.iterMeasure K) ∧
    ∫ ω, ‖M.vF Lphi lam K x ω‖ ^ 2 ∂(M.iterMeasure K) ≤
      (K : ℝ) ^ 4 * Lf ^ 2 / (8 * Lphi ^ 2) + 2 * lam ^ 2 * D ^ 2 := by sorry

end StochHiddenConvex
