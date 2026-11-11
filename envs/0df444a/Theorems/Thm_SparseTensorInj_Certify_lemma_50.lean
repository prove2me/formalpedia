-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_50
-- name    : SparseTensorInj.Certify.lemma_50
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:19.660525+00:00
-- url     : https://prove2.me/theorems/f530f9da-6ca0-4a37-b75a-56a0079c6d15
-- title:
--   Lemma 50 — high-probability bound on the diagonal term $d_{\max}$
-- statement:
--   For every integer $q\ge1$ there is $C_q>0$ such that the following holds. Let $T$ be the random order-$(2q+1)$ tensor of Definition 3 (any $n\ge2q+1$, $\sigma,\gamma>0$), and let $d_{\max}$ be as in Construction 47. Then with probability at least $1-n^{-5}$,
--   $$d_{\max}\le C_q\Big(n\sigma^2+\gamma^2\log n\,\big(\log n+\log(1+\gamma^2/\sigma^2)\big)\Big).$$
--   This controls the diagonal term $2d_{\max}$ of the certificate (9) in the proof of Proposition 44.
--
--   Differences from the source:
--
--   - encoding: with probability at least 1 − n^{-5}, d_max ≤ C_q(…) → the outer probability of the complementary event is at most n^{-5}; reason: complement of the event; identical for the measurable events involved
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 28, Lemma 50

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_RandomModel
import Definitions.Def_SparseTensorInj_Certify_OddCertificate

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 50 (p. 28): for every `q ≥ 1` there is `C_q > 0` such that for the random
order-`(2q+1)` tensor `T` of Definition 3 (any `n ≥ 2q+1`, `σ, γ > 0`), with probability at least
`1 − n^{-5}`, `d_max ≤ C_q (n σ^2 + γ^2 log n (log n + log(1 + γ^2/σ^2)))`. -/
theorem lemma_50 (q : ℕ) (hq : 1 ≤ q) : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 * q + 1 ≤ n →
    ∀ (σ γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (χ : KSubset n (2 * q + 1) → Ω → ℝ),
      IsSubgaussianFamily P χ σ γ →
      P {ω | C * ((n : ℝ) * σ ^ 2 + γ ^ 2 * Real.log n *
          (Real.log n + Real.log (1 + γ ^ 2 / σ ^ 2))) < dmax (modelTensor χ ω)} ≤
        ENNReal.ofReal (((n : ℝ) ^ 5)⁻¹) := by sorry

end SparseTensorInj.Certify
