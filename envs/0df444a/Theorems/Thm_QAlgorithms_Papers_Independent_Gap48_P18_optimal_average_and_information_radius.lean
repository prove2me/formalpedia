-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_optimal_average_and_information_radius
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.optimal_average_and_information_radius
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:37:58.875689+00:00
-- url     : https://prove2.me/theorems/a283d49b-a57b-4279-9286-81074248124c
-- title:
--   Theorem 1
-- statement:
--   For a nonempty set $A$ of density states, write $\bar C(A)$ for its Holevo capacity and $R_A(\sigma)=\sup_{\rho\in A}D(\rho\|\sigma)$. Including infinite capacity,
--
--   $$\bar C(A)=\inf_{\sigma\in\mathfrak S(\mathcal H)}R_A(\sigma)=\inf_{\sigma\in\overline{\operatorname{co}}A}R_A(\sigma).$$
--
--   When $\bar C(A)<\infty$, exactly one state $\Omega(A)$ among all density states satisfies $D(\rho\|\Omega(A))\le\bar C(A)$ for every $\rho\in A$. It belongs to the closed convex hull and $R_A(\Omega(A))=\bar C(A)$. Every capacity-approximating sequence of finite ensembles on $A$ has averages $\bar\rho_n$ with $D(\bar\rho_n\|\Omega(A))\to0$. This defines the optimal average without requiring an optimal ensemble.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 24, Theorem 1

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

/-- Theorem 1, arXiv:quant-ph/0510073v2, PDF pp.24,25.
 -/
theorem optimal_average_and_information_radius {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) :
    setChiCapacity A = (⨅ sigma : State I, radius A sigma) ∧
      setChiCapacity A = (⨅ sigma : stateClosedConvexHull A, radius A sigma.val) ∧
      (setChiCapacity A < ⊤ →
        (∃! omega : State I, RadiusCenter A omega) ∧
        RadiusCenter A (optimalAverage A hA) ∧
        optimalAverage A hA ∈ stateClosedConvexHull A ∧
        radius A (optimalAverage A hA) = setChiCapacity A ∧
        ∀ seq : ℕ → GeneralizedEnsemble I,
          (∀ n, FiniteEnsembleOn (seq n) A) →
          Tendsto (fun n => measureHolevo (seq n : Measure (State I))) atTop (𝓝 (setChiCapacity A)) →
            HConverges (fun n => probabilityAverage (seq n)) (optimalAverage A hA)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
