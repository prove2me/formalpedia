-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition8
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:56:25.88498+00:00
-- url     : https://prove2.me/theorems/83d8c9c3-4c95-4c44-a194-e4743546a2d2
-- title:
--   Intrinsic steerability is monotone on average
-- statement:
--   Let $X$ and $A$ be finite nonempty measurement-choice and outcome alphabets. An assemblage $\hat\rho=\{\hat\rho_B^{a,x}\}_{a,x}$ consists of positive trace-class operators whose sum over $a$ is a trace-one state independent of $x$. Bob’s Hilbert space is unrestricted. Write $S$ and $S^R$ for Definitions 1 and 3, respectively, in bits, with the supremum taken before the infimum over all admissible non-signaling extensions. For every Bob instrument $\{\mathcal K_z\}_z$ with arbitrary output Hilbert space, every input channel $q(x\mid x_f,z)$, and every output channel $r(a_f\mid x_f,x,a,z)$, let $p(z)=\operatorname{Tr}\mathcal K_z(\rho_B)$. For positive-probability branches construct
--
--   $$\hat\rho_z^{a_f,x_f}=\frac{1}{p(z)}\sum_{a,x}r(a_f\mid x_f,x,a,z)q(x\mid x_f,z)\mathcal K_z(\hat\rho^{a,x}).$$
--
--   Then
--
--   $$\sum_{z:p(z)>0}p(z)S(\hat\rho_z)\le S(\hat\rho).$$
--
--   This is average monotonicity for every deterministic one-way LOCC operation. The probabilities are computed from the input assemblage; zero branches are omitted.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 7, Proposition 8, (73)–(75)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- Proposition 8, PDF pp.7--9, (73)--(98): normalized positive branches,
with zero branches omitted. The instrument and classical channels precede inputs. -/
theorem proposition8 : IntrinsicAverageMonotonicity := by sorry

end QAlgorithms.Papers.Independent.Intake100.P10

end
