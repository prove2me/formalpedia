-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_Supplement_doubling_coreset_upper_bound
-- name    : TightCoreset2027.Euclidean.Supplement.doubling_coreset_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:14.778937+00:00
-- url     : https://prove2.me/theorems/fa24dc63-963e-452b-916e-95e35c001936
-- title:
--   Lemma 4.1 — weighted coresets for all queries of at most k centers
-- statement:
--   Fix a real z≥2. There is K>0, depending only on z, such that for every integer k≥1, every real D≥1, every 0<ε<1, every ambient metric space E of doubling dimension at most D, and every finite X⊆E with strictly positive input weights u(p), a nonnegatively weighted subset S⊆X exists with
--
--   $$|S|\le K k^{2-2/z}\varepsilon^{-2}[D\log(2/\varepsilon)+\log(2k)]$$
--
--   and, simultaneously for every finite ambient set C with 1≤|C|≤k,
--
--   $$\left|\sum_{p\in S}w(p)d(p,C)^z-\sum_{p\in X}u(p)d(p,C)^z\right|\le\varepsilon\sum_{p\in X}u(p)d(p,C)^z.$$
--
--   Here d(p,C) is the nearest-center distance. The output is taken on its positive support, so cardinality counts distinct support points. Empty X is allowed and admits the empty output. This is the quantitative new upper branch used for Theorem 1.4; it does not require the theorem's small-error or dimension threshold and imposes no finiteness or compactness on E.
--
--   Differences from the source:
--   - encoding: O_z of the displayed size scale → one positive K chosen before k, D, ε, the metric and both weight functions; reason: footnote 1 and §§4.1–4.2 give uniform z-only constants
--   - encoding: a positively weighted input and a nonnegatively weighted subset, counting support points → finite sets with ambient NNReal weights, positive on X and on the chosen S; reason: discarding zero output weights preserves all costs and cannot increase support; this also handles empty inputs
--   - encoding: ddim(E)≤D and all queries with 1≤|C|≤k → the ambient closed-ball covering predicate and the separate at-most-k weighted coreset predicate; reason: these directly encode the source conventions without an unguarded infinite-space infimum
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Lemma 4.1, printed p. 28 / PDF p. 30; canonical source.pdf SHA256 9c247b18d4e2080420cb421dad0fe6c53b99885cef599b8f8e3cd8d639e13d5f.

import Definitions.Def_TightCoreset2027_Euclidean_Supplement_weightedCoresets
import Definitions.Def_TightCoreset2027_Euclidean_Supplement_doublingGeometry
import Definitions.Def_TightCoreset2027_Euclidean_Supplement_sizeScales
set_option autoImplicit false
universe uUpper

namespace TightCoreset2027.Euclidean.Supplement

/-- Lemma 4.1: arbitrary ambient metric spaces, positive input weights,
and all queries of between one and k centers, with the quantitative bound (31). -/
theorem doubling_coreset_upper_bound (z : ℝ) (hz : 2 ≤ z) :
    ∃ K : ℝ, 0 < K ∧
      ∀ k : ℕ, 1 ≤ k → ∀ D : ℝ, 1 ≤ D →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ (E : Type uUpper) [MetricSpace E], HasDoublingDimensionAtMost E D →
      ∀ (X : Finset E) (u : E → NNReal), (∀ p ∈ X, 0 < u p) →
      ∃ (S : Finset E) (w : E → NNReal),
        IsWeightedAtMostCoreset z ε k X u S w ∧
        (∀ p ∈ S, 0 < w p) ∧
        (S.card : ℝ) ≤ K * upperSizeScale z k ε D := by sorry

end TightCoreset2027.Euclidean.Supplement
