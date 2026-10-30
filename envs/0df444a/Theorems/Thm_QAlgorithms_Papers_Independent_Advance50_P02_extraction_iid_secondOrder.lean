-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_extraction_iid_secondOrder
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.extraction_iid_secondOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:24:43.986012+00:00
-- url     : https://prove2.me/theorems/70d2b200-55a2-41dc-837d-703b0f314b24
-- title:
--   Iid randomness extraction expansion
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Fix a normalized finite CQ source $\rho_{XB}$ and $0<\varepsilon<1$. Let $H=-D(\rho_{XB}\Vert I_X\otimes\rho_B)$ and $V$ be its centered conditional pair variance. For maximal integer extraction length with an independent public seed and the purified-distance security criterion,
--   $$\ell^\varepsilon(X^n|B^n)=nH+\sqrt{nV}\,\Phi^{-1}(\varepsilon^2)+O(\log n).$$
--   The remainder is two-sided with constants before $n$, and includes $V=0$ and singular marginals. The plus sign and squared error distinguish this expansion from compression.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 20, Corollary 16: iid randomness extraction expansion

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

/-- Corollary 16, PDF p.20: plus Phi^-1(epsilon^2), retaining the public seed. Source correction. Printed: Definition 1 p.7 prints V=Tr rho(log rho-log sigma)^2; p.19 prints Gaussian density exp(+x^2/2).
Changed: Use centered V=Tr rho(log rho-log sigma)^2-D^2 and the standard normal density exp(-x^2/2).
Why: Section VI identifies s^2 as Var(Z) and uses the standard normal Berry–Esseen theorem. For pure rho and sigma=I/d the likelihood is constant, hence V=0 even when D=log2(d) is nonzero. -/
theorem extraction_iid_secondOrder (blocks : X → Mat B) (hblocks : NormalizedBlocks blocks)
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    LogarithmicRemainder (fun n => (extractionLength e (blocksPower n blocks) : EReal))
      (fun n => gaussianCenter n (conditionalMean blocks) (cqConditionalVariance blocks) (e^2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
