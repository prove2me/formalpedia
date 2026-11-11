-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_57
-- name    : SparseTensorInj.Certify.lemma_57
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:20.759233+00:00
-- url     : https://prove2.me/theorems/2e542f57-e867-4ae9-881e-5b7c34444630
-- title:
--   Lemma 57 — decoupling: $\mathbb E\,\Phi_t(M)\le4^{2t}\,\mathbb E\,\Phi_t(M_{\mathrm{dec}})$
-- statement:
--   Let $q\ge1$, $n\ge2q+1$, and let $\{\chi_e\}_{e\in E}$, $E=[n]_{2q+1}$, be the coefficients of the random tensor of Definition 3, with $M$ the matrix of Construction 47. Let $\{\chi'_e\}_{e\in E}$ be an independent copy and
--   $$M_{\mathrm{dec}}=\sum_{e,f\in E,\ e\ne f,\ \min_\prec(e)=\min_\prec(f)}\chi_e\chi'_f\,(P_e\otimes P_f).$$
--   Then for every integer $t\ge1$,
--   $$\mathbb E[\Phi_t(M)]\le4^{2t}\,\mathbb E[\Phi_t(M_{\mathrm{dec}})].$$
--   This is the first of the four comparisons combined in Corollary 70.
--
--   Differences from the source:
--
--   - encoding: χ′ an independent copy of the coefficients χ → χ(ω₁) and χ(ω₂) on the product space (Ω × Ω, P ⊗ P); reason: any independent copy gives the same joint law of (χ, χ′), and E[Φ_t(M_dec)] depends only on that law
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 34, Lemma 57

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 57 (p. 34), decoupling: for the random order-`(2q+1)` tensor of Definition 3 and an
independent copy `χ'` of its coefficients, every integer `t ≥ 1` satisfies
`E[Φ_t(M)] ≤ 4^{2t} E[Φ_t(M_dec)]`, `M_dec = Σ_{e ≠ f, min e = min f} χ_e χ'_f (P_e ⊗ P_f)`. -/
theorem lemma_57 (q n : ℕ) (hq : 1 ≤ q) (hn : 2 * q + 1 ≤ n) (σ γ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (χ : KSubset n (2 * q + 1) → Ω → ℝ) (hχ : IsSubgaussianFamily P χ σ γ)
    (t : ℕ) (ht : 1 ≤ t) :
    expPhiM P χ t ≤ 4 ^ (2 * t) * expPhiMdec P χ t := by sorry

end SparseTensorInj.Certify
