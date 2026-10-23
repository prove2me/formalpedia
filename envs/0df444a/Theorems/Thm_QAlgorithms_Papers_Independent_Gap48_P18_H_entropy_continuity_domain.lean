-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_H_entropy_continuity_domain
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.H_entropy_continuity_domain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:54:57.212235+00:00
-- url     : https://prove2.me/theorems/c9f5ad9d-a85a-40ef-9242-1a14093eb5cb
-- title:
--   Remark 1
-- statement:
--   Among finite-entropy density states $\sigma$, the maximal domain of sequential entropy continuity for H-convergence is exactly
--
--   $$\{\sigma:\operatorname{dc}(\sigma)<1\}.$$
--
--   Equivalently, every sequence with $D(\rho_n\|\sigma)\to0$ has $H(\rho_n)\to H(\sigma)$ if and only if $\operatorname{dc}(\sigma)<1$. The finite-entropy domain is the one used in Proposition 2.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 14, Remark 1

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

/-- Remark 1, arXiv:quant-ph/0510073v2, PDF pp.14.
 -/
theorem H_entropy_continuity_domain {I : Type} [Countable I] [Nonempty I]
    (sigma : State I) (hfinite : stateEntropyNats sigma < ⊤) :
    (∀ seq : ℕ → State I, HConverges seq sigma →
      Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 (stateEntropyNats sigma))) ↔
        decreaseCoefficient sigma < 1 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
