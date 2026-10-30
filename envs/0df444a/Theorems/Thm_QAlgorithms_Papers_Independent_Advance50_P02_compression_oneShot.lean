-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_compression_oneShot
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.compression_oneShot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:18:20.565176+00:00
-- url     : https://prove2.me/theorems/2fdb279e-e1f2-4cd2-a08e-50bd92712667
-- title:
--   One-shot source compression
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho_{XB}$ be normalized and classical on $X$, with actual marginal $\rho_B$, and let $0<\eta\le\varepsilon<1$. Compression protocols have an independent seed, a seed-dependent classical encoder to $M$, and a decoder POVM depending on seed and message. Error is averaged over source and seed. Let $m^\varepsilon$ be the smallest integer $m$ with $\log|M|\le m$ and error at most $\varepsilon$. Then
--   $$H_h^\varepsilon(X|B)_\rho\le m^\varepsilon(X|B)_\rho\le H_h^{\varepsilon-\eta}(X|B)_{\rho|\rho}+\log(\varepsilon/\eta^2)+3.$$
--   The right reference is the actual $\rho_B$, whereas the left conditional testing entropy optimizes normalized references. This distinction is needed for the iid limit.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 12, Theorem 9: one-shot source compression

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Theorem 9, PDF pp.11--13: actual marginal in the upper bound. -/
theorem compression_oneShot (blocks : X → Mat B) (hblocks : NormalizedBlocks blocks)
    (e eta : ℝ) (heta : 0 < eta) (hetae : eta ≤ e) (he : e < 1) :
    conditionalTesting e (cqBlockMatrix blocks) ≤ (compressionLength e blocks : EReal) ∧
    (compressionLength e blocks : EReal) ≤
      -extendedTestingDivergence (e-eta) (cqBlockMatrix blocks) (identityTensor X (cqMarginal blocks)) +
        (logTwo (e / eta^2) : ℝ) + 3 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
