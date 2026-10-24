-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P03_covariance_explicit_diagonalization
-- name    : QAlgorithms.Papers.Independent.Support50.P03.covariance_explicit_diagonalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:22:37.564434+00:00
-- url     : https://prove2.me/theorems/b43bb1e5-11dc-443b-96e0-459e2674967e
-- title:
--   Compatible ordinary diagonalization and Gibbs-matrix equivalence
-- statement:
--   Let $n>0$ and let $V$ be a physical real covariance matrix in grouped coordinates $(q_1,\ldots,q_n,p_1,\ldots,p_n)$, with $[x_j,x_k]=i\Omega_{jk}$ and vacuum covariance $I/2$. Thus $V$ is symmetric positive definite and $V+i\Omega/2\ge0$. There exist symplectic eigenvalues $\nu_j\ge1/2$ and a real symplectic matrix $S$, with $S\Omega S^T=\Omega$ and $V=S(D\oplus D)S^T$, where $D=\operatorname{diag}(\nu_j)$. For every such Williamson decomposition, set $U=2^{-1/2}\left[\begin{smallmatrix}1&1\\i&-i\end{smallmatrix}\right]$ and $E=S(U\otimes I_n)$. Then $E$ is invertible and
--
--   $$
--   iV\Omega=E((-D)\oplus D)E^{-1},\qquad S=E(U^\dagger\otimes I_n).
--   $$
--
--   If every $\nu_j>1/2$, set $A=\operatorname{diag}(\operatorname{arcoth}(2\nu_j))$, where $\operatorname{arcoth}(x)=\tfrac12\ln((x+1)/(x-1))$ on $|x|>1$. The primary spectral matrix function obeys
--
--   $$
--   \operatorname{arcoth}(2iV\Omega)=E((-A)\oplus A)E^{-1},\qquad
--   2i\Omega\operatorname{arcoth}(2iV\Omega)=-2\Omega S(A\oplus A)S^T\Omega.
--   $$
--
--   These identities give compatible ordinary eigenvectors and the equivalent Gibbs-matrix formula. Pure modes are included in the diagonalization; the matrix function is asserted on faithful covariances only.
-- source:
--   Gaussian hypothesis testing and quantum illumination, arXiv:1608.06991v2, PDF p. 7, Appendix A, (A4)–(A13)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03

noncomputable section

open Filter

open scoped BigOperators ComplexOrder Topology Matrix

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

/-- Appendix A, arXiv:1608.06991v2, PDF p.7, (A4)--(A13).
Every physical covariance has the displayed COMPATIBLE eigenvectors; arbitrary
ordinary eigenvectors are not assumed to give a real symplectic S. Pure modes
are included in diagonalization. Matrix arcoth and Gibbs identities require
faithfulness; interpolation on distinct eigenvalues gives the primary spectral
matrix function without applying the normal-operator CFC to iVOmega. -/
theorem covariance_explicit_diagonalization (n : ℕ) (hn : 0 < n)
    (V : PhaseMatrix n) (hV : HalfVacuumCovariance V) :
    (∃ (nu : Fin n → ℝ) (S : PhaseMatrix n), GroupedWilliamsonData V nu S) ∧
    (∀ (nu : Fin n → ℝ) (S : PhaseMatrix n), GroupedWilliamsonData V nu S →
      (let E := complexify S * modeEigenbasis n
       IsUnit E.det ∧
       Complex.I • (complexify V * complexify (sigma n)) =
         E * complexify (signedDiagonal nu) * E⁻¹ ∧
       complexify S = E * (modeEigenbasis n).conjTranspose ∧
       (FaithfulSpectrum nu →
         (let B := (2 * Complex.I) • (complexify V * complexify (sigma n))
          spectralArcoth nu B =
            E * complexify (signedDiagonal (fun j => realArcoth (2 * nu j))) * E⁻¹ ∧
          (2 * Complex.I) • (complexify (sigma n) * spectralArcoth nu B) =
            complexify (gibbsMatrix S nu))))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P03

end
