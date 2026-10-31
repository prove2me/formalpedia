-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_quotient_pairing
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.quotient_pairing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:05:05.501555+00:00
-- url     : https://prove2.me/theorems/86244aeb-e13a-47cb-86b3-624eab9b2b8d
-- title:
--   Lemma 5 — quotient pairing
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   Let $\lambda$ be an eigenvalue and $j\ge1$. The kernels in the following quotient spaces are taken within the respective generalized eigenspaces. There is a well-defined bilinear pairing
--   $$\widetilde Q_j:\frac{E_\lambda}{\ker N_\lambda^j}\times\frac{E_{\lambda^{-1}}}{\ker N_{\lambda^{-1}}^j}\longrightarrow\mathbb C,\qquad\widetilde Q_j([v],[w])=\Omega_{\mathbb C}(N_\lambda^jv,w).$$
--   Both its left and right radicals are zero. Large $j$ may give two zero quotient spaces, which are permitted.
--
--
--   This is the nondegenerate reciprocal quotient pairing used to choose cyclic chains.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 8, Lemma 5 — quotient pairing

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

/-- PDF pp.8–9, Lemma 5: existence of the descended bilinear pairing with the
printed formula and BOTH trivial radicals. Zero quotient spaces are allowed. -/
theorem quotient_pairing {n : ℕ} (A : GroupedRealMatrix n) (hA : IsSymplectic A)
    (z : ℂ) (hz : IsEigenvalue A z) (j : ℕ) (hj : 0 < j) :
    ∃ Q : GeneralizedQuotient A z j →ₗ[ℂ] GeneralizedQuotient A z⁻¹ j →ₗ[ℂ] ℂ,
      (∀ (v : generalizedSpace A z) (w : generalizedSpace A z⁻¹),
        Q ((restrictedKernel A z j).mkQ v) ((restrictedKernel A z⁻¹ j).mkQ w) =
          omegaC ((shifted A z ^ j) v.val) w.val) ∧
      (∀ v, (∀ w, Q v w = 0) → v = 0) ∧
      (∀ w, (∀ v, Q v w = 0) → w = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
