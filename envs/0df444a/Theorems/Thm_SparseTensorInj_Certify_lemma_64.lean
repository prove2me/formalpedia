-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_64
-- name    : SparseTensorInj.Certify.lemma_64
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:31.624177+00:00
-- url     : https://prove2.me/theorems/7a8d5ffd-b252-4d17-b05b-5513bd6b1350
-- title:
--   Lemma 64 — symmetrization: $\mathbb E\,\Phi_t(M_{\mathrm{dec}})\le2^{2t}\,\mathbb E\,\Phi_t(M_{\mathrm{sym}})$
-- statement:
--   In the setting of Lemma 57, let $\hat\chi,\hat\chi'$ be independent copies of $\chi,\chi'$ (all four families mutually independent), $\zeta_e=(\chi_e-\hat\chi_e)/\sqrt2$, $\eta_e=(\chi'_e-\hat\chi'_e)/\sqrt2$ (Definition 59), and
--   $$M_{\mathrm{sym}}=\sum_{e,f\in E,\ e\ne f,\ \min_\prec(e)=\min_\prec(f)}\zeta_e\eta_f\,(P_e\otimes P_f).$$
--   Then for every integer $t\ge1$,
--   $$\mathbb E[\Phi_t(M_{\mathrm{dec}})]\le2^{2t}\,\mathbb E[\Phi_t(M_{\mathrm{sym}})].$$
--
--   Differences from the source:
--
--   - encoding: ζ_e = (χ_e − χ̂_e)/√2, η_e = (χ′_e − χ̂′_e)/√2 with χ, χ′, χ̂, χ̂′ four mutually independent copies (Definition 59) → χ(ω₁), χ(ω₂), χ(ω₃), χ(ω₄) on ((Ω × Ω) × (Ω × Ω), (P ⊗ P) ⊗ (P ⊗ P)); reason: same joint law of the four families; E[Φ_t(M_sym)] depends only on it
--   - encoding: χ′ an independent copy of the coefficients χ → χ(ω₁) and χ(ω₂) on the product space (Ω × Ω, P ⊗ P); reason: any independent copy gives the same joint law of (χ, χ′), and E[Φ_t(M_dec)] depends only on that law
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 36, Lemma 64 (Definition 59, p. 35)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 64 (p. 36), symmetrization: with `ζ_e = (χ_e − χ̂_e)/√2`, `η_e = (χ'_e − χ̂'_e)/√2` built
from four mutually independent copies of the coefficients of Definition 3 (Definition 59),
`E[Φ_t(M_dec)] ≤ 2^{2t} E[Φ_t(M_sym)]` for every integer `t ≥ 1`. -/
theorem lemma_64 (q n : ℕ) (hq : 1 ≤ q) (hn : 2 * q + 1 ≤ n) (σ γ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (χ : KSubset n (2 * q + 1) → Ω → ℝ) (hχ : IsSubgaussianFamily P χ σ γ)
    (t : ℕ) (ht : 1 ≤ t) :
    expPhiMdec P χ t ≤ 2 ^ (2 * t) * expPhiMsym P χ t := by sorry

end SparseTensorInj.Certify
