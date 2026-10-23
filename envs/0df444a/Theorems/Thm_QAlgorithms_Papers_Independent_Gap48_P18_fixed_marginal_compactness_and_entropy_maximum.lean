-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_fixed_marginal_compactness_and_entropy_maximum
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.fixed_marginal_compactness_and_entropy_maximum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:50:35.666254+00:00
-- url     : https://prove2.me/theorems/d26f4efc-5d47-4bc6-b064-202078fc425f
-- title:
--   §5.4: coupling compactness and attained entropy supremum
-- statement:
--   For density states $\rho,\sigma$ on arbitrary nonzero separable Hilbert spaces, the full coupling set $C(\rho,\sigma)$ is compact and convex. Including infinite entropies,
--
--   $$\sup_{\omega\in C(\rho,\sigma)}H(\omega)=H(\rho)+H(\sigma),$$
--
--   and the product state $\rho\otimes\sigma$ attains this supremum. This identifies an actual maximizing state, rather than only a numerical supremum.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 62, §5.4: coupling compactness and attained entropy supremum

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

/-- §5.4: coupling compactness and attained entropy supremum, arXiv:quant-ph/0510073v2, PDF pp.62.
 -/
theorem fixed_marginal_compactness_and_entropy_maximum {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (rho : State I) (sigma : State J) :
    IsCompact (couplingSet rho sigma) ∧ CoefficientConvexStates (couplingSet rho sigma) ∧
      entropySup (couplingSet rho sigma) = stateEntropyNats rho + stateEntropyNats sigma ∧
      ∃ tau ∈ couplingSet rho sigma,
        tau.coefficients = productCoeff rho.coefficients sigma.coefficients ∧
        stateEntropyNats tau = entropySup (couplingSet rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
