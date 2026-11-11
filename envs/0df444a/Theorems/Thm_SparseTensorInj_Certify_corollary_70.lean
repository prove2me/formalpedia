-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_corollary_70
-- name    : SparseTensorInj.Certify.corollary_70
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:27.320242+00:00
-- url     : https://prove2.me/theorems/c922a00c-b36e-4aa8-9f07-4f441efd1030
-- title:
--   Corollary 70 — $\mathbb E\,\Phi_t(M)\le(32\sigma^2)^{2t}\,\mathbb E\,\Phi_t(Z)$
-- statement:
--   Let $C_0$ in eq. (10) be a sufficiently large universal constant. Let $T$ be the random order-$(2q+1)$ tensor of Definition 3 ($q\ge1$, $n\ge2q+1$, parameters $\sigma,\gamma>0$), $M$ the matrix of Construction 47, and $Z$ the independent matrix chaos of Definition 68 with entries of law $D_t$, $\rho_t=\sigma^2/B_t^2$. Then for every integer $t\ge1$,
--   $$\mathbb E[\Phi_t(M)]\le(32\sigma^2)^{2t}\,\mathbb E[\Phi_t(Z)].$$
--   It combines Lemmas 57, 64, 66 and 69 ($4\cdot2\cdot4=32$).
--
--   Differences from the source:
--
--   - reading: C_0 > 0 a sufficiently large universal constant in B_t² = C_0(σ² + γ²(t + a)) (eq. (10)) → ∃ C₀* > 0, ∀ C₀ ≥ C₀*, placed before every other quantifier; reason: 'sufficiently large' means every large enough value; 'universal' puts it before q, n, σ, γ and t
--   - encoding: families of mutually independent variables with law D_t (resp. N(0, 1)) → the product measure Measure.pi of sparseRademacher ρ (resp. gaussianReal 0 1) over the index set, one factor per family; reason: same joint law; the expectation depends only on it
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 40, Corollary 70

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Corollary 70 (p. 40): for the universal constant `C₀` of eq. (10) taken large enough, the
matrix `M` of Construction 47 for the random tensor of Definition 3 and the independent matrix
chaos `Z` of Definition 68 (law `D_t`, `ρ_t = σ^2/B_t^2`) satisfy, for every integer `t ≥ 1`,
`E[Φ_t(M)] ≤ (32 σ^2)^{2t} E[Φ_t(Z)]`. -/
theorem corollary_70 : ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ →
    ∀ (q n : ℕ), 1 ≤ q → 2 * q + 1 ≤ n →
    ∀ (σ γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (χ : KSubset n (2 * q + 1) → Ω → ℝ),
      IsSubgaussianFamily P χ σ γ →
      ∀ t : ℕ, 1 ≤ t →
        expPhiM P χ t ≤
          ENNReal.ofReal ((32 * σ ^ 2) ^ (2 * t)) * expPhiZ n q t (rhoT C₀ σ γ t) := by sorry

end SparseTensorInj.Certify
