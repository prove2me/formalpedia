-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_tail_layer_prescribed_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.tail_layer_prescribed_relative_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:52:23.864193+00:00
-- url     : https://prove2.me/theorems/e59eb0f4-6311-4f8e-a87f-04606a298de5
-- title:
--   Lemma 6
-- statement:
--   Let $\sigma=\sum_{k\ge1}\lambda_k|k\rangle\langle k|$ have infinite entropy. Let $L_n(\sigma)$ contain the states with the same diagonal and no off-diagonal entries involving an index below $n$. For every finite $c\ge0$ and integer $n\ge1$,
--
--   $$\exists m,\ \exists\rho\in L_n(\sigma):\quad D(\rho\|\sigma)=c,$$
--
--   with every off-diagonal entry involving an index above $m$ also zero. Thus only a finite band of coherences is needed to realize each prescribed relative entropy.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 59, Lemma 6

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

/-- Lemma 6, arXiv:quant-ph/0510073v2, PDF pp.59.
Source basis index k=1 corresponds to Lean coordinate 0; all inequalities use i+1. Infinite entropy is a hypothesis. -/
theorem tail_layer_prescribed_relative_entropy (sigma : State ℕ)
    (hdiag : Diagonal sigma) (hinfinite : stateEntropyNats sigma = ⊤)
    (c : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (m : ℕ) (rho : State ℕ), rho ∈ tailLayer sigma n ∧
      stateRelativeEntropyNats rho sigma = (c : ℝ≥0∞) ∧
      ∀ i j, i ≠ j → (m < i + 1 ∨ m < j + 1) → rho.coefficients i j = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
