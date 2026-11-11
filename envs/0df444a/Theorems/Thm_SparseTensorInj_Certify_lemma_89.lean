-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_89
-- name    : SparseTensorInj.Certify.lemma_89
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:39:23.601532+00:00
-- url     : https://prove2.me/theorems/1b33a678-6742-4b3a-8ffb-21f9acc99a66
-- title:
--   Lemma 89 — trace moments of the Gaussian reference chaos: $\mathbb E\,\Phi_t(G_s)\le s^{2q}(C_qs^{(2q+1)/2})^{2t}$
-- statement:
--   For every integer $q\ge1$ there is $C_q>0$ such that the following holds. Let $s\ge1$ and $G_s=\sum_{i=1}^sG_i\otimes H_i$, where all entries of $G_1,\dots,G_s,H_1,\dots,H_s\in\mathbb R^{s^q\times s^q}$ are mutually independent standard Gaussians. Then for every integer $1\le t\le s$,
--   $$\mathbb E[\Phi_t(G_s)]\le s^{2q}\big(C_qs^{(2q+1)/2}\big)^{2t}.$$
--   Combined with Lemma 83 and Corollary 70 it gives the trace-moment bound (23) for $M$.
--
--   Differences from the source:
--
--   - encoding: families of mutually independent variables with law D_t (resp. N(0, 1)) → the product measure Measure.pi of sparseRademacher ρ (resp. gaussianReal 0 1) over the index set, one factor per family; reason: same joint law; the expectation depends only on it
--   - encoding: the expectation E[Φ_t(·)] → the lower Lebesgue integral ∫⁻ ENNReal.ofReal(Φ_t(·)) in [0, ∞]; reason: Φ_t ≥ 0, so this is the expectation; no integrability side condition is hidden (all moments here are finite anyway)
--   - encoding: row and column indices in [s^q] → Fin (s ^ q); reason: relabelling
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 52, Lemma 89

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_ChaosMoments

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 89 (p. 52): for every `q ≥ 1` there is `C_q > 0` such that for the Gaussian chaos
`G_s = Σ_{i=1}^s G_i ⊗ H_i` (all entries of `G_i, H_i ∈ ℝ^{s^q × s^q}` independent `N(0, 1)`) and
every integer `1 ≤ t ≤ s`, `E[Φ_t(G_s)] ≤ s^{2q} (C_q s^{(2q+1)/2})^{2t}`. -/
theorem lemma_89 (q : ℕ) (hq : 1 ≤ q) : ∃ C : ℝ, 0 < C ∧
    ∀ s t : ℕ, 1 ≤ t → t ≤ s →
      expPhiG s q t ≤
        ENNReal.ofReal ((s : ℝ) ^ (2 * q) *
          (C * (s : ℝ) ^ ((2 * (q : ℝ) + 1) / 2)) ^ (2 * t)) := by sorry

end SparseTensorInj.Certify
