-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_layer_entropy_and_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.layer_entropy_and_relative_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:37:14.954679+00:00
-- url     : https://prove2.me/theorems/a9cb3c30-df78-4c3c-af4e-bb42c7c2950d
-- title:
--   Proposition 6a
-- statement:
--   Choose an eigenbasis of a density state $\sigma$ and let $L(\sigma)$ consist of all density states with the same diagonal as $\sigma$ in that basis. The layer is compact and convex, and
--
--   $$\sup_{\rho\in L(\sigma)}H(\rho)=H(\sigma).$$
--
--   Entropy is finite and continuous on the layer exactly when $H(\sigma)<\infty$. In that case every $\rho\in L(\sigma)$ has finite entropy and relative entropy, with $D(\rho\|\sigma)=H(\sigma)-H(\rho)$. If $H(\sigma)=\infty$, every pure state in the layer has infinite relative entropy to $\sigma$. This describes entropy within a fixed diagonal layer.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 22, Proposition 6a

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

/-- Proposition 6a, arXiv:quant-ph/0510073v2, PDF pp.22,23.
Chosen eigenbasis is the coordinate basis; hdiag enforces it. Repeated eigenvalues do not erase the choice. The finite difference is written additively after both finiteness conclusions. -/
theorem layer_entropy_and_relative_entropy {I : Type} [Countable I] [Nonempty I]
    (sigma : State I) (hdiag : Diagonal sigma) :
    IsCompact (layer sigma) ∧ CoefficientConvexStates (layer sigma) ∧
      entropySup (layer sigma) = stateEntropyNats sigma ∧
      (FiniteContinuousOn stateEntropyNats (layer sigma) ↔ stateEntropyNats sigma < ⊤) ∧
      (stateEntropyNats sigma < ⊤ → ∀ rho ∈ layer sigma,
        stateEntropyNats rho < ⊤ ∧ stateRelativeEntropyNats rho sigma < ⊤ ∧
          stateRelativeEntropyNats rho sigma + stateEntropyNats rho = stateEntropyNats sigma) ∧
      (stateEntropyNats sigma = ⊤ → ∀ rho : PureState I,
        rho.val ∈ layer sigma → stateRelativeEntropyNats rho.val sigma = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
