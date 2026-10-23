-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P08_williamson_diagonalization
-- name    : QAlgorithms.Papers.Independent.Frontier30.P08.williamson_diagonalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:14:14.207573+00:00
-- url     : https://prove2.me/theorems/09d17d2d-c0a4-41fb-9de0-c17d8f8b5202
-- title:
--   Williamson diagonalization of positive definite matrices
-- statement:
--   Let $N\ge1$ and let $V$ be a real symmetric positive definite $2N\times2N$ matrix. Coordinates are ordered $(q_1,p_1,\ldots,q_N,p_N)$, and $\Omega=\bigoplus_{k=1}^N\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. There exist positive real numbers $\nu_1,\ldots,\nu_N$ and a real symplectic matrix $S$, meaning $S\Omega S^T=\Omega$, such that
--
--   $$V=S\left(\bigoplus_{k=1}^N\nu_k I_2\right)S^T.$$
--
--   The diagonal matrix is a Williamson form and its parameters are the symplectic eigenvalues. This is a matrix theorem; no density operator or uncertainty hypothesis is imposed.
-- source:
--   Gaussian Quantum Information, arXiv:1110.3234v1, PDF p. 9, §II.C.1 Eq.(44): Williamson diagonalization

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P08

open scoped BigOperators ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

/-- PDF p.9, Eq.(44), Williamson's theorem: positive definite means symmetric
positive definite. This is the matrix theorem, so no normal-state premise is added. -/
theorem williamson_diagonalization (n : ℕ) (hn : 0 < n)
    (V : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) (hV : V.PosDef) :
    ∃ nu : Fin n → ℝ, ∃ S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ,
      (∀ k, 0 < nu k) ∧ isSymplectic S ∧
      V = S * williamsonDiagonal nu * S.transpose := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P08

end
