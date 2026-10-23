-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_decreasing_constant_capacity_singleton_intersection
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.decreasing_constant_capacity_singleton_intersection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:53:04.791063+00:00
-- url     : https://prove2.me/theorems/5db94c0c-c718-4d8d-a933-2b6e1bb7cb80
-- title:
--   §5.3: constant positive capacities collapse at intersection
-- statement:
--   Let $\sigma$ have infinite entropy and retain its chosen eigenbasis. Fix a finite $c>0$ and define $A_n=L_{n+1}(\sigma)\cap\{\rho:D(\rho\|\sigma)\le c\}$ for $n\ge0$. These sets are nonempty, compact, convex, and decreasing, and
--
--   $$\bar C(A_n)=c,\qquad\Omega(A_n)=\sigma,\qquad\bigcap_nA_n=\{\sigma\},\qquad\bar C(\bigcap_nA_n)=0.$$
--
--   This concrete family shows that capacity need not be continuous under decreasing intersections.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 61, §5.3: constant positive capacities collapse at intersection

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- §5.3: constant positive capacities collapse at intersection, arXiv:quant-ph/0510073v2, PDF pp.61.
 -/
theorem decreasing_constant_capacity_singleton_intersection (sigma : State ℕ)
    (hdiag : Diagonal sigma) (hinfinite : stateEntropyNats sigma = ⊤)
    (c : ℝ≥0) (hc : 0 < c) :
    (∀ n, decreasingFamily sigma c (n + 1) ⊆ decreasingFamily sigma c n) ∧
      (∀ n, (decreasingFamily sigma c n).Nonempty ∧
        IsCompact (decreasingFamily sigma c n) ∧ CoefficientConvexStates (decreasingFamily sigma c n) ∧
        setChiCapacity (decreasingFamily sigma c n) = (c : ℝ≥0∞) ∧
        ∀ hA : (decreasingFamily sigma c n).Nonempty,
          optimalAverage (decreasingFamily sigma c n) hA = sigma) ∧
      (⋂ n, decreasingFamily sigma c n) = {sigma} ∧
      setChiCapacity (⋂ n, decreasingFamily sigma c n) = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
