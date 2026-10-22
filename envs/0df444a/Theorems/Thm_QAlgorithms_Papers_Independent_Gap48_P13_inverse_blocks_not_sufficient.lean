-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_inverse_blocks_not_sufficient
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.inverse_blocks_not_sufficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:45:49.134291+00:00
-- url     : https://prove2.me/theorems/e35f127b-421c-4f35-912f-baff4b190d22
-- title:
--   Explicit positive covariance disproving sufficiency of the two identities
-- statement:
--   Let each time space be $\mathbb C^2$. Define a Hermitian three-by-three block matrix $A$ by
--
--   $$A_{11}=\operatorname{diag}(4,5),\quad A_{22}=\operatorname{diag}(6,3),\quad A_{33}=\operatorname{diag}(3,1),$$
--
--   $$A_{12}=A_{23}=\begin{pmatrix}1&1\\-2/7&-2/7\end{pmatrix},\qquad A_{13}=\begin{pmatrix}1/14&1/14\\-1/49&-1/49\end{pmatrix},$$
--
--   and $A_{ji}=A_{ij}^*$ for $i<j$. Then $A$ is positive definite and
--
--   $$A_{13}=A_{12}A_{22}^{-1}A_{23}=A_{12}(A_{22}+I)^{-1}A_{23}.$$
--
--   Nevertheless, the ordered imaginary-power identity (40) fails for some real parameter, and the associated quasifree state is not Markovian. Here Markovness means the finite quasifree marginal entropy equality evaluated by $\operatorname{Tr}g$. This explicit covariance shows that the two block identities alone are insufficient.
--
--   Write $B=\operatorname{diag}(A_{12,12},I_3)$, $C=\operatorname{diag}(I_1,A_{22},I_3)$ and $D=\operatorname{diag}(I_1,A_{23,23})$ on the same time space. The ordered identity (40) means
--
--   $$A^{it}(I+A)^{-it}D^{-it}(I+D)^{it}=B^{it}(I+B)^{-it}C^{-it}(I+C)^{it}\quad(t\in\mathbb R).$$
--
--   All these powers in the stated uses have strictly positive spectra.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 17, Example 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Example 2.2, PDF p.17: positivity, both identities (43), and failure of
Markovness for the specified rational matrix. Unbounded density inverse products
in the subsequent background sentence (49) are not asserted. -/
theorem inverse_blocks_not_sufficient :
    let A := counterexampleCovariance
    A.PosDef ∧
    a13 A = a12 A * (a22 A)⁻¹ * a23 A ∧
    a13 A = a12 A * (a22 A + 1)⁻¹ * a23 A ∧
    ¬ PowerCondition A ∧ ¬ IsMarkov A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
