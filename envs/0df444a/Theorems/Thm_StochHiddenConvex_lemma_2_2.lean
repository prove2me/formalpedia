-- Prove2me | Theorems.Thm_StochHiddenConvex_lemma_2_2
-- name    : StochHiddenConvex.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:36.091984+00:00
-- url     : https://prove2.me/theorems/9c034cda-af39-4f9e-9868-7da4a5720878
-- title:
--   Lemma 2.2: bias $\le\frac1{\mu_g}(1-\frac{\mu_g}{cL_\phi})^K$, second moment $\le\frac{K^2}{c^2L_\phi^2}$, expected sample count $\frac{K-1}2$
-- statement:
--   Assume Assumption 2.2(c)(d), Assumption 2.3(b) and the standing monotonicity of $\phi$. Let $c>1$, let $K\ge1$ be an integer, and let $[\nabla\hat g(x)]^{-1}$ be the estimator (9). Then for every $x\in\mathcal X$:
--
--   1. (bias) $\big\|\mathbb E[\nabla\hat g(x)]^{-1}-[\nabla g(x)]^{-1}\big\|\le\dfrac1{\mu_g}\Big(1-\dfrac{\mu_g}{cL_\phi}\Big)^K$;
--   2. (second moment) $\mathbb E\big\|[\nabla\hat g(x)]^{-1}\big\|^2\le\dfrac{K^2}{c^2L_\phi^2}$;
--   3. (cost) the expected number of samples used, $\mathbb E k$, equals $\dfrac{K-1}2$;
--
--   and the expectations in 1 and 2 exist. Because the bias decays geometrically in $K$ while the cost grows linearly, $K=\mathcal O(\log\epsilon^{-1})$ suffices, which is how MSG reaches $\tilde{\mathcal O}(\epsilon^{-2})$ sample complexity.
--
--   Differences from the source:
--   - generalization: ϕᵢ(·, ξᵢ) non-decreasing (p.1, Assumption 2.1(b)) and ϕ(·, ξ) L_ϕ-Lipschitz (Assumption 2.2(c)), stated without a domain for x (read: all of ℝ^d) → required only for x ∈ 𝒳; reason: a condition on ℝ^d implies the same condition on 𝒳, so the statement specializes to the ℝ^d reading; Assumption 2.3 is itself stated on 𝒳 (g : 𝒳 → 𝒰)
--   - reading: for any ξ ∈ Ξ (Assumptions 2.1(b), 2.2(c)) → for ℙ-almost every ξ; reason: Ξ ⊆ ℝ^d is the unspecified set of values of ξ, a set of probability one; the conditions enter only through expectations
--   - reading: Assumption 2.2(d): for any ξ ∈ Ξ, ϕ(x, ξ) is differentiable in x almost surely → for every x ∈ 𝒳, for ℙ-almost every ξ, ϕ(·, ξ) is differentiable at x; reason: the use in the proof of Lemma 2.1 (p.30) and in Appendix D.2 (p.44); the other reading follows from 2.2(c) by Rademacher's theorem and makes Theorem 3.2 false (paper.md)
--   - encoding: ϕ a random function; 𝔼ϕ(x, ξ) and 𝔼∇ϕ(x, ξ) taken without comment; 𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] → ϕᵢ jointly measurable, ϕᵢ(xᵢ, ·) integrable for x ∈ 𝒳, X̲ᵢ ≤ X̄ᵢ (RegularData); reason: the field's standing measurability convention; excludes only data for which the paper's expectations or intervals are undefined
--   - encoding: ∇ϕ(x, ξ) → two-sided derivative of ϕᵢ(·, ξᵢ), with value 0 where it does not exist; reason: by Assumption 2.2(d) the non-differentiable samples are ℙ-null at every x ∈ 𝒳; no expectation changes
--   - encoding: ∇g(x) of g : 𝒳 → 𝒰 → the derivative of gᵢ within [X̲ᵢ, X̄ᵢ] (derivWithin); reason: g is defined on 𝒳; this is the derivative at interior points and the one-sided derivative at faces; together with Assumption 2.3(b) it forces X̲ᵢ < X̄ᵢ, which excludes only degenerate intervals, on which the paper's ∇g is undefined
--   - encoding: ∇ϕ(x, ξ), ∇g(x) and the estimators [∇ĝ(x)]⁻¹ as d × d matrices, with the spectral norm → their diagonal entries carried as vectors; the spectral norm of a diagonal matrix as its largest absolute entry; reason: ϕ is separable, so every matrix involved is diagonal; same values
--   - reading: Assumption 2.2(c)(d) and 2.3(b) → plus the standing monotonicity of ϕ on 𝒳 (p.1); reason: assumed throughout the paper (p.1); the proof uses 0 ⪯ ∇ϕ (p.31) and the second-moment bound fails without it (paper.md)
--   - encoding: [∇g(x)]⁻¹ of Lemma 2.2, which assumes only 2.3(b) → diag(1/gᵢ′(xᵢ)) with gᵢ′ the derivative within [X̲ᵢ, X̄ᵢ]; reason: 2.3(b) with the within-derivative already forces that derivative to exist and be ≥ µ_g > 0
--   - encoding: the number of samples to construct the estimator → k, whose expectation under the estimator's law is computed; reason: k samples are used for a draw of k
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Lemma 2.2, p.14; proof Appendix A.2, pp.31–32

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_Assumptions
import Definitions.Def_StochHiddenConvex_Model_invEst

open MeasureTheory

namespace StochHiddenConvex

/-- **Lemma 2.2 (randomized Neumann-series estimator).** Chen, He, Hu & Ye, arXiv:2205.01774v3,
Lemma 2.2, p.14 (proof Appendix A.2, pp.31–32): "Under Assumption 2.2(c)(d) and Assumption
2.3(b), the bias and the second moment of the estimator (9) with a constant c > 1 satisfy:
‖𝔼[∇ĝ(x)]⁻¹ − [∇g(x)]⁻¹‖ ≤ (1/µ_g)(1 − µ_g/(cL_ϕ))^K, 𝔼‖[∇ĝ(x)]⁻¹‖² ≤ K²/(c²L_ϕ²). Moreover, the
number of samples to construct the estimator in expectation is (K − 1)/2."

All three clauses, at every `x ∈ 𝒳`, every `c > 1` and every integer `K ≥ 1`.

**Formalization Note.** The matrices are diagonal, and the spectral norm of a diagonal matrix is
the largest absolute diagonal entry: the bias bound is stated entrywise, the second moment with
`⨆ i, |·|`. `[∇g(x)]⁻¹ = diag(1/gᵢ′(xᵢ))`. The standing monotonicity of p.1 is included (the
proof uses `0 ⪯ ∇ϕ`, p.31). The number of samples is `k`, whose mean is computed. -/
theorem lemma_2_2 {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P] (Lphi μg : ℝ)
    (hreg : M.RegularData) (h21b : M.MonotoneOnBox)
    (h22c : M.Assumption22c Lphi) (h22d : M.Assumption22d) (h23b : M.Assumption23b μg)
    (c : ℝ) (hc : 1 < c) (K : ℕ) (hK : 1 ≤ K) (x : Vec d) (hx : x ∈ M.box) :
    (∀ i, Integrable (fun ω => M.invEst c Lphi K x ω.1 ω.2 i) (M.estMeasure K) ∧
      |(∫ ω, M.invEst c Lphi K x ω.1 ω.2 i ∂(M.estMeasure K)) - (M.dg i (x i))⁻¹| ≤
        1 / μg * (1 - μg / (c * Lphi)) ^ K) ∧
    Integrable (fun ω => (⨆ i, |M.invEst c Lphi K x ω.1 ω.2 i|) ^ 2) (M.estMeasure K) ∧
    ∫ ω, (⨆ i, |M.invEst c Lphi K x ω.1 ω.2 i|) ^ 2 ∂(M.estMeasure K) ≤
      (K : ℝ) ^ 2 / (c ^ 2 * Lphi ^ 2) ∧
    ∫ ω, ((ω.1 : ℕ) : ℝ) ∂(M.estMeasure K) = ((K : ℝ) - 1) / 2 := by sorry

end StochHiddenConvex
