-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_66
-- name    : SparseTensorInj.Certify.lemma_66
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:22.389245+00:00
-- url     : https://prove2.me/theorems/f32b9c12-be65-432e-a515-623f988bb585
-- title:
--   Lemma 66 — moment domination: $\mathbb E\,\Phi_t(M_{\mathrm{sym}})\le\sigma^{4t}\,\mathbb E\,\Phi_t(M_{\mathrm{comp}})$
-- statement:
--   Let $C_0$ in eq. (10) be a sufficiently large universal constant. In the setting of Lemma 64 ($q\ge1$, $n\ge2q+1$, coefficients of Definition 3 with parameters $\sigma,\gamma>0$), let $t\ge1$ be an integer, $\rho_t=\sigma^2/B_t^2$, and let $\{\mu_e\},\{\nu_e\}$ be two independent families of independent variables with the scaled sparse Rademacher law $D_t$ (Definition 62), and
--   $$M_{\mathrm{comp}}=\sum_{e,f\in E,\ e\ne f,\ \min_\prec(e)=\min_\prec(f)}\mu_e\nu_f\,(P_e\otimes P_f)$$
--   (Definition 65). Then
--   $$\mathbb E[\Phi_t(M_{\mathrm{sym}})]\le\sigma^{4t}\,\mathbb E[\Phi_t(M_{\mathrm{comp}})].$$
--
--   Differences from the source:
--
--   - reading: C_0 > 0 a sufficiently large universal constant in B_t² = C_0(σ² + γ²(t + a)) (eq. (10)) → ∃ C₀* > 0, ∀ C₀ ≥ C₀*, placed before every other quantifier; reason: 'sufficiently large' means every large enough value; 'universal' puts it before q, n, σ, γ and t
--   - encoding: ζ_e = (χ_e − χ̂_e)/√2, η_e = (χ′_e − χ̂′_e)/√2 with χ, χ′, χ̂, χ̂′ four mutually independent copies (Definition 59) → χ(ω₁), χ(ω₂), χ(ω₃), χ(ω₄) on ((Ω × Ω) × (Ω × Ω), (P ⊗ P) ⊗ (P ⊗ P)); reason: same joint law of the four families; E[Φ_t(M_sym)] depends only on it
--   - encoding: families of mutually independent variables with law D_t (resp. N(0, 1)) → the product measure Measure.pi of sparseRademacher ρ (resp. gaussianReal 0 1) over the index set, one factor per family; reason: same joint law; the expectation depends only on it
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 37, Lemma 66 (Definitions 62 and 65, pp. 36–37)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 66 (p. 37), moment comparison: for the universal constant `C₀` of eq. (10) taken large
enough, for the coefficients of Definition 3 and every integer `t ≥ 1`,
`E[Φ_t(M_sym)] ≤ σ^{4t} E[Φ_t(M_comp)]`, where `M_comp` uses independent variables with the
scaled sparse Rademacher law `D_t` of parameter `ρ_t = σ^2/B_t^2` (Definitions 62, 65). -/
theorem lemma_66 : ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ →
    ∀ (q n : ℕ), 1 ≤ q → 2 * q + 1 ≤ n →
    ∀ (σ γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (χ : KSubset n (2 * q + 1) → Ω → ℝ),
      IsSubgaussianFamily P χ σ γ →
      ∀ t : ℕ, 1 ≤ t →
        expPhiMsym P χ t ≤
          ENNReal.ofReal (σ ^ (4 * t)) * expPhiMcomp n q t (rhoT C₀ σ γ t) := by sorry

end SparseTensorInj.Certify
