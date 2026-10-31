-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_complex_normal_form_catalogue
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.complex_normal_form_catalogue
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:15:49.518597+00:00
-- url     : https://prove2.me/theorems/5679538b-b0a5-4c21-a35e-131b7f4bb6eb
-- title:
--   Unnumbered complex symplectic block catalogue
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   Put $P=\operatorname{diag}(J(\bar\lambda,k),J(\lambda,k))$ and $D=D(k,s)$. The complex matrix in (23) is $\left(\begin{smallmatrix}P^{-1}&P^{-1}\left(\begin{smallmatrix}0&D\\D&0\end{smallmatrix}\right)\\0&P^T\end{smallmatrix}\right)$.
--   Put $P=\operatorname{diag}(J(\bar\lambda,k),J(\lambda,k+1))$ and let $S$ be the $k\times(k+1)$ matrix with only its last row possibly nonzero, ending in $(is/2,\lambda is)$. The complex matrix in (27) is $\left(\begin{smallmatrix}P^{-1}&P^{-1}\left(\begin{smallmatrix}0&S\\S^T&0\end{smallmatrix}\right)\\0&P^T\end{smallmatrix}\right)$. At $k=0$ the rectangular sectors are empty.
--   There is a complex symplectic basis of $V_{\mathbb C}$ representing $A$ as a finite symplectic direct sum of the following three families:
--   $$B(\lambda,k,s),\qquad\text{the paired matrix (23)},\qquad\text{the unequal matrix (27)}.$$
--   The single family has real off-circle eigenvalues, $k\ge1,s=0$, or $\lambda=\pm1$, $k\ge1,s\in\{-1,0,1\}$ with $s=0$ requiring $k$ odd. The paired family has nonreal off-circle eigenvalues, $k\ge1,s=0$, or nonreal unit eigenvalues, $k\ge1,s=\pm1$. The unequal family has nonreal unit eigenvalues, $k\ge0,s=\pm1$. Every parameter is an actual eigenvalue, the block dimensions exhaust the ambient dimension, and the multiset of nonzero signs is called the sign characteristic.
--
--
--   This preserves all three introductory complex matrix types with the precise spectral regimes from the full theorem.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 3, Unnumbered complex symplectic block catalogue

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

/-- PDF p.3: introductory complex block catalogue with ALL three types;
spectral/sign restrictions come from the precise real theorem on pp.4–6. -/
theorem complex_normal_form_catalogue {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A) :
    ∃ (L : ℕ) (c : Fin L → CatalogueBlock),
      (∀ j, CatalogueValid A (c j)) ∧
      RepresentsC A ⊤ (symplecticBlockSum (fun j => catalogueSize (c j)) fun j => catalogueMatrix (c j)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
