-- Prove2me | Theorems.Thm_TightCoreset2027_Euclidean_Supplement_doubling_coreset_lower_bound
-- name    : TightCoreset2027.Euclidean.Supplement.doubling_coreset_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:09:38.263429+00:00
-- url     : https://prove2.me/theorems/63bd6feb-0f87-4b0a-8dc9-1eebf02f7ca3
-- title:
--   Lemma 3.1 — coreset lower bound at every prescribed doubling dimension
-- statement:
--   Fix a real exponent z≥2. There exist constants 0<c₁≤c₂, C>0 and 0<ε₀<1, depending only on z. For every integer k≥1, every 0<ε≤ε₀ and every prescribed real D≥C log(2/ε), there are a finite ambient metric space E and an unweighted finite dataset X⊆E such that, with F(z,k,ε,D)=kD min{k^(1−2/z) ε^(−2), ε^(−z)},
--
--   $$D/8\le\operatorname{ddim}(E)\le D,\qquad c_1 F(z,k,\varepsilon,D)\le |X|\le c_2 F(z,k,\varepsilon,D).$$
--
--   For every subset S⊆X with arbitrary nonnegative weights w, if S preserves the clustering cost of every ambient set of exactly k distinct centers to relative error ε, then
--
--   $$2|S|>|X|.$$
--
--   This supplies the lower direction of companion Theorem 1.4, including z=2 and noninteger z>2, both branches of the minimum and the accuracy endpoint ε=ε₀. Dimension is measured on the whole ambient metric, including its available centers; no sampling law or bound on the output weights is imposed.
--
--   Differences from the source:
--   - encoding: the comparison |X| ≍ F with z-only constants → positive c₁≤c₂ and thresholds C, ε₀ quantified before k, ε, D; reason: footnote 1 and §3.4 fix these constants once per z
--   - encoding: an arbitrary finite ambient metric space with actual doubling dimension → a metric on Fin N and log₂ of its attained least positive integer closed-ball covering constant; reason: every finite metric can be relabeled this way; this retains the exact D/8 and D bounds
--   - encoding: weights on a finite subset and |S|>|X|/2 → ambient NNReal weight functions, Finset cardinalities and X.card<2*S.card; reason: extension of weights changes no query; the integer inequality is exactly the strict half bound
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), Lemma 3.1, printed p. 21 / PDF p. 23; canonical source.pdf SHA256 9c247b18d4e2080420cb421dad0fe6c53b99885cef599b8f8e3cd8d639e13d5f.

import Definitions.Def_TightCoreset2027_Euclidean_coresetModel
import Definitions.Def_TightCoreset2027_Euclidean_Supplement_doublingGeometry
import Definitions.Def_TightCoreset2027_Euclidean_Supplement_sizeScales
set_option autoImplicit false

namespace TightCoreset2027.Euclidean.Supplement

/-- Lemma 3.1: every prescribed real dimension, the full size comparison,
and the strict half-support obstruction against arbitrary nonnegative reweightings. -/
theorem doubling_coreset_lower_bound (z : ℝ) (hz : 2 ≤ z) :
    ∃ c₁ c₂ C ε₀ : ℝ,
      0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ D : ℝ, C * Real.log (2 / ε) ≤ D →
      ∃ (N : ℕ) (metric : MetricSpace (Fin N)),
        letI : MetricSpace (Fin N) := metric
        ∃ X : Finset (Fin N),
          D / 8 ≤ finiteDoublingDimension (Fin N) ∧
          finiteDoublingDimension (Fin N) ≤ D ∧
          c₁ * doublingSizeScale z k ε D ≤ (X.card : ℝ) ∧
          (X.card : ℝ) ≤ c₂ * doublingSizeScale z k ε D ∧
          ∀ (S : Finset (Fin N)) (w : Fin N → NNReal),
            IsStrongCoreset z ε k X S w → X.card < 2 * S.card := by sorry

end TightCoreset2027.Euclidean.Supplement
