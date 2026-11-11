-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_49
-- name    : SparseTensorInj.Certify.lemma_49
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:02.110325+00:00
-- url     : https://prove2.me/theorems/6e94d9fa-ea7d-441b-8331-5a8711474ed0
-- title:
--   Lemma 49 — moments of a subgaussian variable retain the variance factor $\sigma^2$
-- statement:
--   Let $C_0$ in eq. (10) be a sufficiently large universal constant. Let $\sigma,\gamma>0$, let $t\ge1$ be an integer, and let $X$ be a random variable with $\mathbb E[X^2]\le\sigma^2$ and $\|X\|_{\psi_2}\le\gamma$. Then, with $B_t^2=C_0(\sigma^2+\gamma^2(t+\log(1+\gamma^2/\sigma^2)))$,
--   $$\mathbb E\big[|X|^{2r}\big]\le\sigma^2B_t^{2r-2}\qquad\text{for all integers }1\le r\le t .$$
--   A standard subgaussian bound would give $(C\gamma^2r)^r$ and lose the factor $\sigma^2$; keeping it is what produces the leading term $\sigma n^{k/4}$. The lemma feeds Lemma 50 and, through Corollary 61, Lemma 66.
--
--   Differences from the source:
--
--   - reading: C_0 > 0 a sufficiently large universal constant in B_t² = C_0(σ² + γ²(t + a)) (eq. (10)) → ∃ C₀* > 0, ∀ C₀ ≥ C₀*, placed before every other quantifier; reason: 'sufficiently large' means every large enough value; 'universal' puts it before q, n, σ, γ and t
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 28, Lemma 49 (with eq. (10), p. 27)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_RandomModel
import Definitions.Def_SparseTensorInj_Certify_MomentParams

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 49 (p. 28): for the universal constant `C₀` of eq. (10) taken large enough, every
random variable `X` with `E[X^2] ≤ σ^2` and `‖X‖_{ψ2} ≤ γ` (`σ, γ > 0`) satisfies, for every
integer `t ≥ 1`, `E[|X|^{2r}] ≤ σ^2 B_t^{2r−2}` for all `1 ≤ r ≤ t`, where
`B_t^2 = C₀ (σ^2 + γ^2 (t + log(1 + γ^2/σ^2)))`. -/
theorem lemma_49 : ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ →
    ∀ (σ γ : ℝ) (t : ℕ), 0 < σ → 0 < γ → 1 ≤ t →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ),
      Measurable X → ∫ ω, X ω ^ 2 ∂P ≤ σ ^ 2 → Psi2Le P X γ →
      ∀ r : ℕ, 1 ≤ r → r ≤ t →
        ∫ ω, |X ω| ^ (2 * r) ∂P ≤ σ ^ 2 * Bsq C₀ σ γ t ^ (r - 1) := by sorry

end SparseTensorInj.Certify
