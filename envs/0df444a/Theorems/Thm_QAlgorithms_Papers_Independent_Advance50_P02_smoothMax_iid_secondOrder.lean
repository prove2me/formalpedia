-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_smoothMax_iid_secondOrder
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.smoothMax_iid_secondOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:30:47.327994+00:00
-- url     : https://prove2.me/theorems/d34e8bf2-62ca-4fd3-8533-76ea5d37bcd9
-- title:
--   Smooth max-relative iid expansion
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be normalized and $\sigma\ge0$ with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Fix $0<\varepsilon<1$, let $D=D(\rho\Vert\sigma)$ and let $V$ be the centered information variance. Then
--   $$D_{\max}^\varepsilon(\rho^{\otimes n}\Vert\sigma^{\otimes n})=nD-\sqrt{nV}\,\Phi^{-1}(\varepsilon^2)+O(\log n).$$
--   The error is a two-sided bound with positive constant and threshold before $n$. It includes zero variance, singular $\rho$, and unnormalized $\sigma$. This is the smooth counterpart of the testing expansion.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 19, §VI-A Eq. (35): smooth max-relative iid expansion

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

/-- Eq.(35), PDF pp.6,19: minus Phi^-1(epsilon^2), full support domain and V=0. Source correction. Printed: Definition 1 p.7 prints V=Tr rho(log rho-log sigma)^2; p.19 prints Gaussian density exp(+x^2/2).
Changed: Use centered V=Tr rho(log rho-log sigma)^2-D^2 and the standard normal density exp(-x^2/2).
Why: Section VI identifies s^2 as Var(Z) and uses the standard normal Berry–Esseen theorem. For pure rho and sigma=I/d the likelihood is constant, hence V=0 even when D=log2(d) is nonzero. -/
theorem smoothMax_iid_secondOrder (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (hsupport : SupportIncluded rho sigma)
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    LogarithmicRemainder
      (fun n => smoothedMaxRelativeEntropy e (tensorPower n rho) (tensorPower n sigma))
      (fun n => n * relativeMean rho sigma -
        Real.sqrt ((n : ℝ)*centeredRelativeVariance rho sigma) * normalQuantile (e^2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
