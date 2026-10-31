-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_normalized_chain_pairing_identities
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.normalized_chain_pairing_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:06:06.649982+00:00
-- url     : https://prove2.me/theorems/1391b342-8576-4ebf-bdc5-cd01cd8f3ad3
-- title:
--   Definition 7 and equations (16)–(17) — normalized chain pairings
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For $|\lambda|=1$, define
--   $$T_{ij}(v)=\frac{\Omega_{\mathbb C}(N_\lambda^i v,N_{\bar\lambda}^j\bar v)}{\lambda^i\bar\lambda^j},\qquad i,j\ge0.$$
--   For an eigenvalue $\lambda$ of unit norm and $v\in E_\lambda$,
--   $$T_{ij}(v)=-T_{i+1,j}(v)-T_{i+1,j-1}(v)\quad(j>0),\qquad T_{ij}(v)=-\overline{T_{ji}(v)}\quad(i,j\ge0).$$
--
--
--   These identities normalize conjugate chain pairings; the recurrence is not asserted at $j=0$.
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 10, Definition 7 and equations (16)–(17) — normalized chain pairings

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

/-- PDF p.10, Definition 7 and (16)–(17): recurrence only at j>0;
the conjugate-swap identity includes the printed MINUS sign. -/
theorem normalized_chain_pairing_identities {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (z : ℂ) (hz : ‖z‖ = 1) (he : IsEigenvalue A z)
    (v : CVec n) (hv : v ∈ generalizedSpace A z) :
    (∀ i j : ℕ, 0 < j → chainT A z v i j =
      -chainT A z v (i + 1) j - chainT A z v (i + 1) (j - 1)) ∧
    (∀ i j : ℕ, chainT A z v i j = -star (chainT A z v j i)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
