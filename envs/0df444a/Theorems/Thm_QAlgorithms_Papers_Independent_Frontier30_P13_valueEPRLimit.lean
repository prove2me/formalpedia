-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P13_valueEPRLimit
-- name    : QAlgorithms.Papers.Independent.Frontier30.P13.valueEPRLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:18:40.348988+00:00
-- url     : https://prove2.me/theorems/ec00918d-6a71-41fe-af40-d0692d60cba4
-- title:
--   The finite EPR covariance family has vanishing asymptotic value
-- statement:
--   Fix an integer $n\ge1$. Let $\Lambda=\operatorname{diag}(1,-1,\ldots,1,-1)$ on $2n$ interleaved coordinates and define the finite covariance family
--
--   $$\gamma_n(r)=\begin{pmatrix}\cosh(r)I_{2n}&\sinh(r)\Lambda\\\sinh(r)\Lambda&\cosh(r)I_{2n}\end{pmatrix}.$$
--
--   For the bipartition between its two $n$-mode registers, the variational scale $V$ satisfies
--
--   $$\lim_{r\to+\infty}V(\gamma_n(r))=0.$$
--
--   This is a limit of covariance quantities of finite physical systems. It does not postulate a normalizable state at infinite squeezing.
-- source:
--   The characterization of Gaussian operations and Distillation of Gaussian States, arXiv:quant-ph/0204085v4, PDF p. 7, Appendix A(3), Eq.(A4): vanishing V at infinite squeezing

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

/-- Appendix A, PDF p.7, Eq.(A4), with Section II, PDF p.2, Eq.(4): V tends
to zero along the finite EPR covariance family. No infinite-energy state or
trace-norm convergence to an improper vector is asserted. -/
theorem valueEPRLimit (n : ℕ) (hn : 0 < n) :
    Tendsto (fun r : ℝ => valueV (squeezedCM n r)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P13

end
