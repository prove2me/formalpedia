-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_signed_real_normal_form
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.signed_real_normal_form
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:09:23.130552+00:00
-- url     : https://prove2.me/theorems/f02d7765-3e03-4864-bd4d-0fb6f3d395e4
-- title:
--   Theorem 10 — signed normal form at +/-1
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For an eigenvalue $a\in\{1,-1\}$ there are finitely many positive lengths $r_j$ and integers $s_j\in\{-1,0,1\}$, with $s_j=0$ implying $r_j$ odd, and an actual symplectic basis of $V_{[a]}$ such that
--   $$A|_{V_{[a]}}=\mathop{\diamond}_j B(a,r_j,s_j),\qquad\dim\ker(A-aI)=2\#\{j:s_j=0\}+\#\{j:s_j\ne0\}.$$
--
--
--   This is the signed Jordan representation and exact lambda-kernel count required by the first supporting interface. The printed final eigenvalue “1” is corrected to “lambda”.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 17, Theorem 10 — signed normal form at +/-1

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

/-- PDF p.17, Theorem 10. Printed: final sentence says eigenvalue 1.
Changed: eigenvalue lambda. Why: Theorem 1 p.5 and the proof count lambda,
and the literal claim is false at lambda=-1. Zero signs permit EVERY odd r. -/
theorem signed_real_normal_form {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (a : ℝ) (ha : a = 1 ∨ a = -1) (he : IsEigenvalue A (a : ℂ)) :
    ∃ (L : ℕ) (r : Fin L → ℕ) (s : Fin L → ℤ),
      RealNormal A a r s ∧ RealKernelCount A a s := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
