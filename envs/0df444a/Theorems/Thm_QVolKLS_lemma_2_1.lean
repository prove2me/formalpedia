-- Prove2me | Theorems.Thm_QVolKLS_lemma_2_1
-- name    : QVolKLS.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:40:44.822208+00:00
-- url     : https://prove2.me/theorems/5ca43405-b29b-426d-9485-d32b706fb8af
-- title:
--   Lemma 2.1 — covariance comparison: $(16B)^{-1}\mathrm{Cov}_\mu\preceq\mathrm{Cov}_\nu\preceq16B\,\mathrm{Cov}_\mu$
-- statement:
--   Let $\mu,\nu$ be full-dimensional log-concave probability laws on $\mathbb R^D$ satisfying
--   $$
--   \int\Big(\frac{d\nu}{d\mu}\Big)^2d\mu\le B,\qquad \int\Big(\frac{d\mu}{d\nu}\Big)^2d\nu\le B .
--   $$
--   Then
--   $$
--   (16B)^{-1}\,\mathrm{Cov}_\mu(X)\ \preceq\ \mathrm{Cov}_\nu(X)\ \preceq\ 16B\,\mathrm{Cov}_\mu(X)
--   $$
--   in the Loewner order, i.e. $(16B)^{-1}\mathrm{Var}_\mu\langle u,X\rangle\le\mathrm{Var}_\nu\langle u,X\rangle\le16B\,\mathrm{Var}_\mu\langle u,X\rangle$ for every $u\in\mathbb R^D$.
--
--   This lets a covariance estimate at one cooling stage precondition the next ([KV06, Lemma 4.3]).
--
--   **Formalization Note** Log-concavity is the published Borell compact-set form; full-dimensional is absolute continuity with respect to Lebesgue measure.
--
--   Differences from the source:
--   - encoding: log-concave: density ∝ e^{−V} with V convex; full-dimensional → FunctionalInequalities.KLS.LogConcave (Borell's compact-set inequality) and µ, ν ≪ volume; reason: for laws absolutely continuous with respect to Lebesgue measure the two definitions agree (Borell 1975)
--   - encoding: the densities dν/dµ and dµ/dν → explicit hypotheses ν ≪ µ and µ ≪ ν; reason: the hypotheses of the lemma presuppose these densities exist
--   - encoding: ∫ (dν/dµ)² dµ ≤ B → lower Lebesgue integral of the Radon–Nikodym derivative squared ≤ B in ℝ≥0∞; reason: an infinite integral is not read as 0
--   - encoding: Loewner order of covariance matrices → the order on every quadratic form u ↦ Var(⟨u, X⟩); reason: Cov ⪯ Cov′ iff uᵀCov u ≤ uᵀCov′u for all u
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 2.1, p.22

import Definitions.Def_QVolKLS_logAffineZ
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave

set_option autoImplicit false

namespace QVolKLS

open MeasureTheory
open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 2.1 (Covariance comparison
[KV06, Lemma 4.3])**, p.22. Let `µ`, `ν` be full-dimensional log-concave laws on `ℝ^D` with
`∫ (dν/dµ)² dµ ≤ B` and `∫ (dµ/dν)² dν ≤ B`. Then
`(16B)^{−1} Cov_µ(X) ⪯ Cov_ν(X) ⪯ 16B Cov_µ(X)`.

**Formalization Note.** Log-concave is the published `FunctionalInequalities.KLS.LogConcave` (Borell's
compact-set form; for laws absolutely continuous with respect to Lebesgue measure it is the paper's
"density proportional to `e^{−V}`, `V` convex", p.22). Full-dimensional is `≪ volume`. The densities
`dν/dµ`, `dµ/dν` presuppose mutual absolute continuity, assumed explicitly; the two integrals are
lower Lebesgue integrals in `ℝ≥0∞` (so an infinite integral is not read as `0`). The Loewner order is
stated on every quadratic form `u ↦ uᵀ Cov u = Var(⟨u, X⟩)` (`dirVariance`). -/
theorem lemma_2_1 {D : ℕ} (μ ν : ProbabilityMeasure (Euc D)) (B : ℝ)
    (hμ : FunctionalInequalities.KLS.LogConcave μ) (hν : FunctionalInequalities.KLS.LogConcave ν)
    (hμvol : (μ : Measure (Euc D)) ≪ volume) (hνvol : (ν : Measure (Euc D)) ≪ volume)
    (hνμ : (ν : Measure (Euc D)) ≪ (μ : Measure (Euc D)))
    (hμν : (μ : Measure (Euc D)) ≪ (ν : Measure (Euc D)))
    (h1 : ∫⁻ x, ((ν : Measure (Euc D)).rnDeriv (μ : Measure (Euc D)) x) ^ 2 ∂(μ : Measure (Euc D))
      ≤ ENNReal.ofReal B)
    (h2 : ∫⁻ x, ((μ : Measure (Euc D)).rnDeriv (ν : Measure (Euc D)) x) ^ 2 ∂(ν : Measure (Euc D))
      ≤ ENNReal.ofReal B) :
    ∀ u : Euc D,
      (16 * B)⁻¹ * dirVariance (μ : Measure (Euc D)) u ≤ dirVariance (ν : Measure (Euc D)) u ∧
      dirVariance (ν : Measure (Euc D)) u ≤ 16 * B * dirVariance (μ : Measure (Euc D)) u := by sorry

end QVolKLS
