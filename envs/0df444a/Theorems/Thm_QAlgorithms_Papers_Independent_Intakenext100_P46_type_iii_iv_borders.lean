-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_type_iii_iv_borders
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.type_iii_iv_borders
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:05:33.517979+00:00
-- url     : https://prove2.me/theorems/58875d9e-353d-4faf-b5bb-c23ce7870b92
-- title:
--   §5, Eq. (39) and following display: exceptional and symmetric border constructions
-- statement:
--   For $\gamma_A,\gamma_B\ge1/2$ put $\delta=(\gamma_A^2-1/4)(\gamma_B^2-1/4)$ and $D=\operatorname{diag}(\gamma_A,\gamma_B,\gamma_A,\gamma_B)$. The two exceptional blocks are
--   $$Q_L=\begin{pmatrix}(1+\delta/\gamma_A^2)^{1/4}&0\\[\delta^2/(\gamma_A^2(\gamma_B^2+\delta))]^{1/4}&[\gamma_B^2/(\gamma_B^2+\delta)]^{1/4}\end{pmatrix},$$
--   $$Q_U=\begin{pmatrix}[\gamma_A^2/(\gamma_A^2+\delta)]^{1/4}&[\delta^2/(\gamma_B^2(\gamma_A^2+\delta))]^{1/4}\\0&(1+\delta/\gamma_B^2)^{1/4}\end{pmatrix}.$$
--   The symmetric block is $Q_S=2^{-1/2}\begin{pmatrix}s_1&s_2\\s_1&-s_2\end{pmatrix}$, where
--   $$s_1=\left[\frac{4\gamma_A^2(4\gamma_B^2+1)}{4\gamma_A^2+1}\right]^{1/4},\qquad s_2=\left[\frac{4\gamma_B^2+1}{4\gamma_B^2(4\gamma_A^2+1)}\right]^{1/4}.$$
--   For each block $Q$, $S=Q\oplus Q^{-T}$ is symplectic and $SDS^T$ is physical and lies on the actual Gaussian separability border. If both normal eigenvalues exceed $1/2$, its finite EM is $S^{-T}\operatorname{diag}(m,m)S^{-1}$ with $m_j=\ln((2\gamma_j+1)/(2\gamma_j-1))$. The symmetric covariance has the half-covariance form with nonnegative correlations and $(m-k_q)(m-k_p)=1$. In the strict chart each triangular covariance has standard form with positive $c_1,c_2$ and $a/b=c_1/c_2$ or $a/b=c_2/c_1$. These are constructed families, with no type-III same-type minimizer assertion. The finite exponential matrix refers to the actual normalized Gibbs density: after a bounded unitary implementing the stated symplectic transformation, its number-basis weights are $\prod_j(1-e^{-m_j})e^{-m_j n_j}$. This operator meaning is part of the conclusion, alongside the covariance normal form.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 9, §5, Eq. (39) and following display: exceptional and symmetric border constructions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P46

open scoped BigOperators ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (finiteRelativeEntropy compression entropyWeight)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation bipartiteCharacteristic bipartiteWeyl gaussianStateCharacteristic)

-- These accepted definitions have the same completed Hilbert-space meaning.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P41 (IsDiagonal)

/-- Chen, PDF pp.3,9, (39) and following display: two exceptional triangular
border constructions and the symmetric border family. The numerators contain
delta^2, whereas the diagonal fractions contain delta. These are candidate
families, not a same-type minimizer theorem for a type-III input. -/
theorem type_iii_iv_borders (gA gB : ℝ) (hA : 1 / 2 ≤ gA) (hB : 1 / 2 ≤ gB) :
    (∀ Sq ∈ ({exceptionalLower gA gB, exceptionalUpper gA gB,
        symmetricBorderQ gA gB} : Set (Matrix Two Two ℝ)),
      IsSymplecticMatrix (symplecticLift Sq) ∧ IsPhysicalCovariance (borderCMFrom Sq gA gB) ∧
      CovBorder (borderCMFrom Sq gA gB) ∧
      (1 / 2 < gA → 1 / 2 < gB →
        GaussianEM (borderCMFrom Sq gA gB) (emFrom (symplecticLift Sq) (pairValues gA gB)))) ∧
    (∃ m kq kp : ℝ, 0 ≤ kq ∧ 0 ≤ kp ∧
      borderCMFrom (symmetricBorderQ gA gB) gA gB = symmetricCM m kq kp ∧
      (m - kq) * (m - kp) = 1) ∧
    (1 / 2 < gA → 1 / 2 < gB →
      ∀ Sq ∈ ({exceptionalLower gA gB, exceptionalUpper gA gB} : Set (Matrix Two Two ℝ)),
        ∃ a b c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧
          borderCMFrom Sq gA gB = standardCM a b c1 c2 ∧
          (a / b = c1 / c2 ∨ a / b = c2 / c1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
