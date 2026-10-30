-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_testing_iid_secondOrder
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.testing_iid_secondOrder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:11:48.927811+00:00
-- url     : https://prove2.me/theorems/84d25776-5c19-4870-96d7-bd1530702b9a
-- title:
--   Two-sided iid quantum hypothesis-testing expansion
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be a normalized quantum state and $\sigma\ge0$ a comparison operator on the same space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Fix $0<\varepsilon<1$. Let $D=D(\rho\Vert\sigma)$ and $V=\operatorname{tr}\rho(\log\rho-\log\sigma)^2-D^2$ be the centered information variance, and let $\Phi^{-1}$ denote the standard normal quantile. There are constants $C>0$ and $n_0\ge2$, depending only on this fixed pair and error, such that for every $n\ge n_0$,
--   $$
--    nD+\sqrt{nV}\,\Phi^{-1}(\varepsilon)-C\log n
--    \le D_h^\varepsilon(\rho^{\otimes n}\Vert\sigma^{\otimes n})
--    \le nD+\sqrt{nV}\,\Phi^{-1}(\varepsilon)+C\log n.
--   $$
--   The statement includes $V=0$, singular states and unnormalized comparisons. It supplies the full two-sided logarithmic-remainder testing interface.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 19, §VI-A Eq. (34): two-sided iid hypothesis-testing expansion (seed headline)

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

/-- Eq.(34), PDF pp.6,19: full support domain, singular rho and unnormalized sigma,
including V=0. Two-sided constants precede n. Source correction. Printed: Definition 1 p.7 prints V=Tr rho(log rho-log sigma)^2; p.19 prints Gaussian density exp(+x^2/2).
Changed: Use centered V=Tr rho(log rho-log sigma)^2-D^2 and the standard normal density exp(-x^2/2).
Why: Section VI identifies s^2 as Var(Z) and uses the standard normal Berry–Esseen theorem. For pure rho and sigma=I/d the likelihood is constant, hence V=0 even when D=log2(d) is nonzero. -/
theorem testing_iid_secondOrder (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (hsupport : SupportIncluded rho sigma)
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    LogarithmicRemainder
      (fun n => extendedTestingDivergence e (tensorPower n rho) (tensorPower n sigma))
      (fun n => gaussianCenter n (relativeMean rho sigma) (centeredRelativeVariance rho sigma) e) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
