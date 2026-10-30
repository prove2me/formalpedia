-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_compression_iid_secondOrder
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.compression_iid_secondOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:23:53.04598+00:00
-- url     : https://prove2.me/theorems/a24bbfda-2d0c-4fe0-a257-7382a2500d5a
-- title:
--   Iid compression expansion
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Fix a normalized finite CQ source $\rho_{XB}$ and $0<\varepsilon<1$. Define $H=-D(\rho_{XB}\Vert I_X\otimes\rho_B)$ and the centered pair variance $V$ for this same pair, using the actual marginal. For the integer compression optimum defined using all seeded encoders and conditional decoder POVMs,
--   $$m^\varepsilon(X^n|B^n)=nH-\sqrt{nV}\,\Phi^{-1}(\varepsilon)+O(\log n).$$
--   The remainder is a two-sided bound with positive constant and threshold chosen before $n$. Neither positive variance nor a full-rank marginal is required. This yields the second-order compression cost.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 20, Corollary 15: iid compression expansion

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

/-- Corollary 15, PDF p.20: actual marginal, integer compression length, V=0 allowed. Source correction. Printed: Definition 1 p.7 prints V=Tr rho(log rho-log sigma)^2; p.19 prints Gaussian density exp(+x^2/2).
Changed: Use centered V=Tr rho(log rho-log sigma)^2-D^2 and the standard normal density exp(-x^2/2).
Why: Section VI identifies s^2 as Var(Z) and uses the standard normal Berry–Esseen theorem. For pure rho and sigma=I/d the likelihood is constant, hence V=0 even when D=log2(d) is nonzero. -/
theorem compression_iid_secondOrder (blocks : X → Mat B) (hblocks : NormalizedBlocks blocks)
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    LogarithmicRemainder (fun n => (compressionLength e (blocksPower n blocks) : EReal))
      (fun n => n * conditionalMean blocks -
        Real.sqrt ((n : ℝ)*cqConditionalVariance blocks) * normalQuantile e) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
