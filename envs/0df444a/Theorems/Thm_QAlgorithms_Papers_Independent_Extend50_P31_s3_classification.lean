-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_s3_classification
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.s3_classification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:59:25.105371+00:00
-- url     : https://prove2.me/theorems/c4ca2509-f6c3-451c-b136-ee747431b0ab
-- title:
--   Section 8.3 and introduction Eq.(4): S(3) channel classification
-- statement:
--   Use the $S_3$ doublet $U((12))=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $U((23))=\begin{pmatrix}0&w^2\\w&0\end{pmatrix}$, where $w=e^{2\pi i/3}$. All its covariant channels have real parameters $s=l_{\mathrm{sgn}}$, $t=l_\lambda$, with
--
--   $$
--   \operatorname{mat}\Phi_{s,t}=\frac12\begin{pmatrix}1+s&0&0&1-s\\0&2t&0&0\\0&0&2t&0\\1-s&0&0&1+s\end{pmatrix},\qquad\Phi_{s,t}\text{ is a channel}\ \Longleftrightarrow\ -1\le s\le1,\quad |t|\le\frac{1+s}{2}.
--   $$
--
--   The Choi matrix is $J(\Phi_{s,t})=\begin{pmatrix}(1+s)/2&0&0&t\\0&(1-s)/2&0&0\\0&0&(1-s)/2&0\\t&0&0&(1+s)/2\end{pmatrix}$. In order $\mathrm{id},\mathrm{sgn},\lambda_1,\lambda_2$, its eigenvalues are $((1+s)/2+t,(1+s)/2-t,(1-s)/2,(1-s)/2)$. The rectangular transform is $M=\frac12\begin{pmatrix}1&1&2\\1&1&-2\\1&-1&0\\1&-1&0\end{pmatrix}$; $N=\frac12\begin{pmatrix}1&1&1&1\\1&1&-1&-1\\1&-1&0&0\end{pmatrix}$ satisfies $NM=I_3$. A Kraus family is $\sqrt{\epsilon_{\mathrm{id}}/2}I$, $\sqrt{\epsilon_{\mathrm{sgn}}/2}\operatorname{diag}(-1,1)$, $\sqrt{(1-s)/2}E_{21}$, $\sqrt{(1-s)/2}E_{12}$. It reconstructs the map and is normalized. These maps are unital, trace-preserving and covariant for all real parameters, and CP exactly on the stated triangle.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 27, Section 8.3 and introduction Eq.(4): S(3) channel classification

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF pp.4,26--27 Eqs.(4),(137)--(143): complete choiEigenvalueVector-family classification,
including the explicit map, spectral constraints, rectangular transform and Kraus formula. -/
theorem s3_classification (U : UnitaryIrrep (Equiv.Perm (Fin 3)) 2)
    (hU : EpsilonRealization U) :
    (∀ Phi : EndMat 2, (IsIrrepCovariant U Phi ∧ IsPaperChannel Phi) ↔
      ∃ s t : ℝ, Phi = s3Map s t ∧ S3CP s t) ∧
    (∀ s t : ℝ, IsIrrepCovariant U (s3Map s t) ∧ TracePreserving (s3Map s t) ∧ s3Map s t 1 = 1 ∧
      rowMatrixRepresentative (s3Map s t) = tensorFour ((1/2 : ℂ) •
        !![1+(s : ℂ),0,0,1-(s : ℂ);0,2*(t : ℂ),0,0;0,0,2*(t : ℂ),0;1-(s : ℂ),0,0,1+(s : ℂ)]) ∧
      choi (s3Map s t) = tensorFour
        !![(1+s)/2,0,0,t;0,(1-s)/2,0,0;0,0,(1-s)/2,0;t,0,0,(1+s)/2] ∧
      HasOrthonormalSpectrum (choi (s3Map s t)) (s3Eigenvalues s t) ∧
      ((choi (s3Map s t)).PosSemidef ↔ S3CP s t) ∧
      (IsPaperChannel (s3Map s t) ↔ S3CP s t) ∧
      s3Transform.mulVec ![1,(s:ℂ),(t:ℂ)] = (fun r => (s3Eigenvalues s t r : ℂ)) ∧
      (S3CP s t → QAlgorithms.IsKrausFamily (s3Kraus s t) ∧
        ∀ X : Mat 2, s3Map s t X = QAlgorithms.krausApply (s3Kraus s t) X)) ∧
    s3Inverse * s3Transform = 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
