-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_finite_union_capacity_bounds
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.finite_union_capacity_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:51:46.034429+00:00
-- url     : https://prove2.me/theorems/537c38c6-9db3-4165-b63f-bc4df34d4fdc
-- title:
--   Proposition 7
-- statement:
--   Let $A_1,\ldots,A_n$ be nonempty sets of density states, $n\ge1$. Always,
--
--   $$\bar C(\bigcup_kA_k)\le\max_k\bar C(A_k)+\log n.$$
--
--   If all component capacities are finite, the simplex objective $J(\lambda)=\sum_k\lambda_k\bar C(A_k)+\chi(\{\lambda_k,\Omega(A_k)\})$ attains a maximum and
--
--   $$\max_{\lambda\in\Delta_n}J(\lambda)\le\bar C(\bigcup_kA_k).$$
--
--   If every capacity equals a finite $C$, this gives $C+\bar C(\{\Omega(A_k)\})\le\bar C(\bigcup_kA_k)\le C+\log n$. The maximum is attained, rather than merely a supremum.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 36, Proposition 7

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

/-- Proposition 7, arXiv:quant-ph/0510073v2, PDF pp.36.
Upper bound permits infinite component capacities; every occurrence of optimal averages is under finite-component assumptions. -/
theorem finite_union_capacity_bounds {I : Type} [Countable I] [Nonempty I]
    (n : ℕ) (hn : 0 < n) (A : Fin n → Set (State I)) (hA : ∀ k, (A k).Nonempty) :
    setChiCapacity (⋃ k, A k) ≤ (⨆ k, setChiCapacity (A k)) + ENNReal.ofReal (Real.log n) ∧
      ((∀ k, setChiCapacity (A k) < ⊤) →
        (∃ w : Fin n → ℝ≥0, InSimplex w ∧
          (∀ v : Fin n → ℝ≥0, InSimplex v → unionObjective A hA v ≤ unionObjective A hA w) ∧
          unionObjective A hA w ≤ setChiCapacity (⋃ k, A k)) ∧
        (∀ C : ℝ≥0, (∀ k, setChiCapacity (A k) = (C : ℝ≥0∞)) →
          (C : ℝ≥0∞) + setChiCapacity (Set.range (fun k => optimalAverage (A k) (hA k))) ≤
            setChiCapacity (⋃ k, A k) ∧
          setChiCapacity (⋃ k, A k) ≤ (C : ℝ≥0∞) + ENNReal.ofReal (Real.log n))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
