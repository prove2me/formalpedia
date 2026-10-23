-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_regularity_alternatives_independent
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.regularity_alternatives_independent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:51:14.68584+00:00
-- url     : https://prove2.me/theorems/c31fb2ec-ff47-40cd-8dd8-793281429316
-- title:
--   §4.2: independence of the two regularity conditions
-- statement:
--   The two defining regularity alternatives are independent in infinite dimension. There is a nonempty finite-capacity set for which entropy at $\Omega(A)$ is finite and converges along every H-convergent closed-hull sequence, while $D(\cdot\|\Omega(A))$ is not finite continuous on $A$. There is also a nonempty finite-capacity set with the reverse behavior:
--
--   $$\exists A:\ R_1(A)\land\neg R_2(A),\qquad\exists B:\ R_2(B)\land\neg R_1(B).$$
--
--   Here $R_1,R_2$ are exactly the two alternatives of Definition 2. Regularity uses their disjunction.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 29, §4.2: independence of the two regularity conditions

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

/-- §4.2: independence of the two regularity conditions, arXiv:quant-ph/0510073v2, PDF pp.29.
 -/
theorem regularity_alternatives_independent {I : Type} [Countable I] [Infinite I] :
    (∃ (A : Set (State I)) (hA : A.Nonempty), setChiCapacity A < ⊤ ∧
      RegularityOne A (optimalAverage A hA) ∧
      ¬ RegularityTwo A (optimalAverage A hA)) ∧
    (∃ (A : Set (State I)) (hA : A.Nonempty), setChiCapacity A < ⊤ ∧
      RegularityTwo A (optimalAverage A hA) ∧
      ¬ RegularityOne A (optimalAverage A hA)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
