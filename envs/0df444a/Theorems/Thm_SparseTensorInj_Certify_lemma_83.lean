-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_83
-- name    : SparseTensorInj.Certify.lemma_83
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:19.011869+00:00
-- url     : https://prove2.me/theorems/d53bc44f-e072-4a6d-bcb6-f5c759b9107d
-- title:
--   Lemma 83 — Gaussian comparison with dimension compression: $\mathbb E\,\Phi_t(Z)\le\frac{N_q^2}{s^{2q}\rho^{2t}}\mathbb E\,\Phi_t(G_s)$ (for every $\rho\in(0,1]$)
-- statement:
--   Let $q\ge1$, $n\ge2q+1$, $N_q=\binom nq$, let $t\ge1$ be an integer and $\rho\in(0,1]$. Let $Z$ be the independent matrix chaos of Definition 68 with entries of the scaled sparse Rademacher law of parameter $\rho$, and $G_s=\sum_{i=1}^sG_i\otimes H_i$ the Gaussian chaos of Definition 79 with reference dimension
--   $$s=\big\lceil n\rho^{2/(2q+1)}\big\rceil+2t .$$
--   Then
--   $$\mathbb E[\Phi_t(Z)]\le\frac{N_q^2}{s^{2q}\rho^{2t}}\,\mathbb E[\Phi_t(G_s)].$$
--   The paper states it for $\rho=\rho_t=\sigma^2/B_t^2$; the compressed dimension $s$ is what makes the final bound variance-sensitive.
--
--   Differences from the source:
--
--   - generalization: the parameter ρ_t = σ²/B_t² of D_t → every ρ ∈ (0, 1]; reason: the statement involves σ, γ, C_0, t only through ρ_t, which lies in (0, 1] (Definition 62 notes ρ_t ≤ 1); the paper's statement is the instance ρ = ρ_t
--   - encoding: families of mutually independent variables with law D_t (resp. N(0, 1)) → the product measure Measure.pi of sparseRademacher ρ (resp. gaussianReal 0 1) over the index set, one factor per family; reason: same joint law; the expectation depends only on it
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: N_q = |I_q| and G_i, H_i ∈ ℝ^{s^q × s^q} with indices in [s^q] → Nat.choose n q, and Fin (s ^ q) as the row and column index type; reason: |I_q| = C(n, q); relabelling
--   - encoding: the ceiling ⌈nρ^{2/(2q+1)}⌉ → the natural-number ceiling ⌈·⌉₊; reason: the argument is non-negative, where both ceilings agree
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 46, Lemma 83 (Definition 79, p. 44)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 83 (p. 46), Gaussian comparison with dimension compression: for an integer `t ≥ 1` and
`s = ⌈n ρ^{2/(2q+1)}⌉ + 2t`, `E[Φ_t(Z)] ≤ (N_q^2 / (s^{2q} ρ^{2t})) E[Φ_t(G_s)]`, where
`N_q = C(n, q)`, `Z` is the chaos of Definition 68 with law `D` of parameter `ρ`, and `G_s` is the
Gaussian chaos of Definition 79; stated for every `ρ ∈ (0, 1]` (the paper's `ρ_t = σ^2/B_t^2`). -/
theorem lemma_83 (q n t : ℕ) (hq : 1 ≤ q) (hn : 2 * q + 1 ≤ n) (ht : 1 ≤ t)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    let s : ℕ := ⌈(n : ℝ) * ρ ^ ((2 : ℝ) / (2 * (q : ℝ) + 1))⌉₊ + 2 * t
    expPhiZ n q t ρ ≤
      ENNReal.ofReal ((Nat.choose n q : ℝ) ^ 2 / ((s : ℝ) ^ (2 * q) * ρ ^ (2 * t))) *
        expPhiG s q t := by sorry

end SparseTensorInj.Certify
