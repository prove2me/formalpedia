-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_extraction_oneShot
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.extraction_oneShot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:17:14.320995+00:00
-- url     : https://prove2.me/theorems/3f4090ec-bc16-46d1-b10a-ecd36f2a5606
-- title:
--   One-shot randomness extraction and all-protocol converse
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho_{XB}$ be normalized and classical on $X$, and let $0<\eta\le\varepsilon<1$. A protocol applies a seed-dependent hash $X\to Z$ with an independent public seed $S$. Its security is $\min_{\sigma_B}P(\tau_{SZB},\tau_S\otimes\pi_Z\otimes\sigma_B)$, with one normalized reference $\sigma_B$ shared across seeds. Let $\ell^\varepsilon$ be the maximal integer length achievable with $\log|Z|\ge\ell$ and security at most $\varepsilon$. Then
--   $$H_{\min}^{\varepsilon-\eta}(X|B)-\log(1/\eta^4)-3\le\ell^\varepsilon(X|B)\le H_{\min}^\varepsilon(X|B).$$
--   For every individual protocol, the supporting converse (9) also gives
--   $$\log|Z|>H_{\min}^\varepsilon(X|B)\ \Longrightarrow\ d_{\rm sec}>\varepsilon.$$
--   This characterizes extraction while retaining the public seed in the security criterion.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 10, Theorem 8: one-shot randomness extraction

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

/-- Theorem 8, PDF pp.10--11: public-seed security and integer lengths. -/
theorem extraction_oneShot (blocks : X → Mat B) (hblocks : NormalizedBlocks blocks)
    (e eta : ℝ) (heta : 0 < eta) (hetae : eta ≤ e) (he : e < 1) :
    positiveTraceSmoothedMinEntropy (e-eta) (cqBlockMatrix blocks) - (logTwo (1 / eta^4) : ℝ) - 3 ≤
      (extractionLength e blocks : EReal) ∧
    (extractionLength e blocks : EReal) ≤ positiveTraceSmoothedMinEntropy e (cqBlockMatrix blocks) ∧
    (∀ P : Extractor X, positiveTraceSmoothedMinEntropy e (cqBlockMatrix blocks) < (logTwo P.outputs : EReal) →
      e < extractionSecurity P blocks) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
