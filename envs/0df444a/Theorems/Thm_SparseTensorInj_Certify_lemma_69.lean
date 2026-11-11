-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_69
-- name    : SparseTensorInj.Certify.lemma_69
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:23.014221+00:00
-- url     : https://prove2.me/theorems/eec5d172-2217-45c6-9400-d3b12601a066
-- title:
--   Lemma 69 — orientation: $\mathbb E\,\Phi_t(M_{\mathrm{comp}})\le4^{2t}\,\mathbb E\,\Phi_t(Z)$ (for every sparsity $\rho\in(0,1]$)
-- statement:
--   Let $q\ge1$, $n\ge2q+1$, let $t\ge1$ be an integer, and let $D$ be the scaled sparse Rademacher law with parameter $\rho\in(0,1]$ ($\pm\rho^{-1/2}$ with probability $\rho/2$ each, $0$ otherwise). Let $M_{\mathrm{comp}}$ be the chaos of Definition 65 with $D$-distributed coefficients, and $Z=\sum_{i\in[n]}X_i\otimes Y_i$ the independent matrix chaos of Definition 68 (all entries of $X_i,Y_i\in\mathbb R^{N_q\times N_q}$ mutually independent with law $D$). Then
--   $$\mathbb E[\Phi_t(M_{\mathrm{comp}})]\le4^{2t}\,\mathbb E[\Phi_t(Z)].$$
--   The paper states it for $\rho=\rho_t=\sigma^2/B_t^2$.
--
--   Differences from the source:
--
--   - generalization: the parameter ρ_t = σ²/B_t² of D_t → every ρ ∈ (0, 1]; reason: the statement involves σ, γ, C_0, t only through ρ_t, which lies in (0, 1] (Definition 62 notes ρ_t ≤ 1); the paper's statement is the instance ρ = ρ_t
--   - encoding: families of mutually independent variables with law D_t (resp. N(0, 1)) → the product measure Measure.pi of sparseRademacher ρ (resp. gaussianReal 0 1) over the index set, one factor per family; reason: same joint law; the expectation depends only on it
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 39, Lemma 69 (Definition 68, p. 38)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 69 (p. 39), orientation: for the independent matrix chaos `Z = Σ_i X_i ⊗ Y_i` of
Definition 68 and every integer `t ≥ 1`, `E[Φ_t(M_comp)] ≤ 4^{2t} E[Φ_t(Z)]`; here stated for
every sparse Rademacher parameter `ρ ∈ (0, 1]` (the paper's `ρ_t` is one such value). -/
theorem lemma_69 (q n t : ℕ) (hq : 1 ≤ q) (hn : 2 * q + 1 ≤ n) (ht : 1 ≤ t)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    expPhiMcomp n q t ρ ≤ 4 ^ (2 * t) * expPhiZ n q t ρ := by sorry

end SparseTensorInj.Certify
