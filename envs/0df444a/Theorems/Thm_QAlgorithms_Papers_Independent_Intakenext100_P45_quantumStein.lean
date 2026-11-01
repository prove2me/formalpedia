-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumStein
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumStein
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:21:40.339996+00:00
-- url     : https://prove2.me/theorems/079026d2-0c52-49f3-94f2-320a31777ce6
-- title:
--   §5.6, quantum Stein lemma
-- statement:
--   For arbitrary finite-dimensional densities $\rho,\sigma$ and fixed $0<\varepsilon<1$, define $\beta_n^*(\varepsilon)$ as the infimum of $\operatorname{Tr}((I-P)\sigma^{\otimes n})$ over all joint effects satisfying $\operatorname{Tr}(P\rho^{\otimes n})\le\varepsilon$. Then
--
--   $$\lim_{n\to\infty}-\frac1n\log\beta_n^*(\varepsilon)=S(\rho\|\sigma).$$
--
--   The extended limit exists, independently of $\varepsilon$, including the infinite value on support failure.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 30, §5.6, quantum Stein lemma

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.30,31: §5.6, quantum Stein lemma. -/
theorem quantumStein (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1) :
    HasRate (constrainedTypeII rho sigma eps) (relativeEntropy rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
