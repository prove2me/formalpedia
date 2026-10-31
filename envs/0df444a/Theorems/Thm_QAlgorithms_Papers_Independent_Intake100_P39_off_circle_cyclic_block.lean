-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_off_circle_cyclic_block
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.off_circle_cyclic_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:07:13.827028+00:00
-- url     : https://prove2.me/theorems/cff23725-b55f-4275-bd56-732a1890f721
-- title:
--   Unnumbered off-circle paired-chain block construction
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $z\in\mathbb C$, write $R(z)=\left(\begin{smallmatrix}\Re z&-\Im z\\\Im z&\Re z\end{smallmatrix}\right)$. The real Jordan matrix $J_R(z,2r)$ has $R(z)$ on its $2\times2$ diagonal blocks, $I_2$ on its block superdiagonal, and zeros elsewhere.
--   Let $\lambda$ be an off-circle eigenvalue, let $p$ be the maximal height on $E_\lambda$, and choose $v\in E_\lambda$, $w\in E_{\lambda^{-1}}$ with $\Omega_{\mathbb C}(N_\lambda^pv,w)\ne0$. Let $E_\lambda^v=\operatorname{span}_{\mathbb C}\{N_\lambda^jv:j\ge0\}$ and define $E_{\lambda^{-1}}^w$ similarly. The sum has a complex symplectic basis with matrix
--   $$\operatorname{diag}(J(\lambda,p+1)^{-1},J(\lambda,p+1)^T).$$
--   If $\lambda,v,w$ are real, its real part has a real symplectic basis with that matrix. If $\lambda$ is nonreal, adjoining the conjugate cyclic spaces gives a constructed real subspace with symplectic matrix
--   $$\operatorname{diag}(J_R(\bar\lambda,2(p+1))^{-1},J_R(\bar\lambda,2(p+1))^T).$$
--   The terminal action is $Aa_p=\lambda a_p$, correcting the p.11 typo.
--
--
--   This supplies both realifications of an individual paired cyclic block.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 11, Unnumbered off-circle paired-chain block construction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse only the pinned accepted substrate, with definitionally identical coordinate models.
-- The imported symplectic predicate preserves -Omega0, equivalent to preserving Omega0.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

/-- PDF pp.11–13: paired cyclic construction, including real and nonreal realification.
Printed A a_p=a_p on p.11 is changed to lambda a_p, as used on p.13. -/
theorem off_circle_cyclic_block {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ ≠ 1) (he : IsEigenvalue A z) (p : ℕ) (hp : HasNilpotentHeight A z p)
    (v w : CVec n) (hv : v ∈ generalizedSpace A z) (hw : w ∈ generalizedSpace A z⁻¹)
    (hpair : omegaC ((shifted A z ^ p) v) w ≠ 0) :
    RepresentsC A (cyclicC A z v ⊔ cyclicC A z⁻¹ w) (signedBlock z (p + 1) 0) ∧
    (z.im = 0 → (∃ vr : RVec n, realEmbed n vr = v) →
      (∃ wr : RVec n, realEmbed n wr = w) →
      RepresentsR A (realPart (cyclicC A z v ⊔ cyclicC A z⁻¹ w))
        (signedBlock z.re (p + 1) 0)) ∧
    (z.im ≠ 0 → RepresentsR A
      (realPart ((cyclicC A z v ⊔ cyclicC A z⁻¹ w) ⊔
        (cyclicC A (star z) (star v) ⊔ cyclicC A (star (z⁻¹)) (star w))))
      (offComplexBlock z (p + 1))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
