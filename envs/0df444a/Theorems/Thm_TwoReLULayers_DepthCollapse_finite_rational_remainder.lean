-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_finite_rational_remainder
-- name    : TwoReLULayers.DepthCollapse.finite_rational_remainder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:00.502127+00:00
-- url     : https://prove2.me/theorems/951b015f-6a3b-462d-a82d-e262fb8e8f42
-- title:
--   Finite rational remainder in the simplex decomposition
-- statement:
--   For every $n\ge2$, there are finitely many nonempty rational polytopes $Q_i$ of affine dimension at most $n-2$ and rational scalars $c_i$ such that, on all real inputs,
--   $$h_\Delta(x)=\frac{(-1)^n}{n!}\sum_{v,\pi,M}(-1)^{|M|}h_{K_{v,\pi,M}}(x)+\sum_i c_i h_{Q_i}(x).$$
--   This exposes actual finite witnesses and their coefficient field. A merely real-span remainder would not suffice to deduce rational network weights.
--
--   Differences from the source:
--   - encoding: finite Euclidean coordinates and finite index families → EuclideanSpace ℝ (Fin n), Fin k and pointwise function identities; reason: canonical coordinate identification and reindexing preserve every source instance
--   - encoding: vertex labels 1,...,n and marked positions 2,...,n-1 → zero-based Fin labels, bijective Order v and positive-valued marked positions; reason: subtracting one from labels and positions is a bijective reindexing; position one remains unconstrained
--   - encoding: rational vertices → IsPolytopeOver (⊥ : Subfield ℝ); reason: the prime subfield of ℝ is exactly ℚ; the predicate requires an actual nonempty finite rational convex-hull witness
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 9, Section 1.3, displayed remainder identity; Section 8, p. 24, rational conclusion

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem finite_rational_remainder {n : ℕ} (hn : 2 ≤ n) :
    ∃ k : ℕ, ∃ c : Fin k → ℚ, ∃ Q : Fin k → Set (E n),
      (∀ i, IsPolytopeOver (⊥ : Subfield ℝ) (Q i) ∧ affineDim (Q i) ≤ n - 2) ∧
      ∀ x : E n, support (simplex n) x =
        ((-1 : ℝ) ^ n / (Nat.factorial n : ℝ)) * signedKSupports n x +
          ∑ i, (c i : ℝ) * support (Q i) x := by sorry

end TwoReLULayers.DepthCollapse
