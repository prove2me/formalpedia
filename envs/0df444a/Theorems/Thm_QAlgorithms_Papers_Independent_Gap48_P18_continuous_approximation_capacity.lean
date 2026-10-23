-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_continuous_approximation_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.continuous_approximation_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:41:23.857673+00:00
-- url     : https://prove2.me/theorems/58c7ae1e-a5e4-4b4d-98da-227f17ea0018
-- title:
--   Lemma 4
-- statement:
--   Let $\Lambda$ be a nonempty directed preordered index set. Suppose continuous state maps $\Psi_\lambda$ tend pointwise to the identity on a nonempty set $A$. Then
--
--   $$\liminf_\lambda\bar C(\Psi_\lambda(A))\ge\bar C(A).$$
--
--   If these capacities converge to the finite value $\bar C(A)$ and the image capacities are eventually finite, their optimal averages converge in trace norm to $\Omega(A)$. The maps need not be affine or channels.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 37, Lemma 4

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

/-- Lemma 4, arXiv:quant-ph/0510073v2, PDF pp.37.
 -/
theorem continuous_approximation_capacity {I L : Type} [Countable I] [Nonempty I]
    [Preorder L] [Nonempty L] (hdirected : (∀ x y : L, ∃ z : L, x ≤ z ∧ y ≤ z))
    (A : Set (State I)) (hA : A.Nonempty) (Psi : L → State I → State I)
    (hcontinuous : ∀ l, Continuous (Psi l))
    (hpointwise : ∀ rho ∈ A, Tendsto (fun l => Psi l rho) atTop (𝓝 rho)) :
    setChiCapacity A ≤ Filter.liminf (fun l => setChiCapacity (Psi l '' A)) atTop ∧
      (setChiCapacity A < ⊤ →
        (∀ᶠ l in atTop, setChiCapacity (Psi l '' A) < ⊤) →
        Tendsto (fun l => setChiCapacity (Psi l '' A)) atTop (𝓝 (setChiCapacity A)) →
        Tendsto (fun l => optimalAverage (Psi l '' A) (hA.image (Psi l))) atTop
          (𝓝 (optimalAverage A hA))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
