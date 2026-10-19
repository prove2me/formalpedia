-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P08_physicality_williamson
-- name    : QAlgorithms.Papers.Independent.Frontier30.P08.physicality_williamson
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:14:40.751597+00:00
-- url     : https://prove2.me/theorems/31cbb886-d584-4685-b64a-8804a2e36696
-- title:
--   Uncertainty in Williamson coordinates
-- statement:
--   Let $N\ge1$ and let $V$ be a real symmetric $2N\times2N$ matrix in interleaved quadrature coordinates. In units $\hbar=2$, let $\Omega$ be the direct sum of $N$ copies of $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Then
--
--   $$V+i\Omega\succeq0\quad\Longleftrightarrow\quad V\succ0\ \text{and}\ \exists S,\nu:\ S\Omega S^T=\Omega,\quad V=S\left(\bigoplus_k\nu_k I_2\right)S^T,\quad\nu_k\ge1\ \text{for all }k.$$
--
--   Thus the uncertainty inequality is exactly the lower bound one on the Williamson spectrum of a positive definite covariance. The Williamson data on the right are conclusions of the characterization. The pure boundary $\nu_k=1$ is retained.
-- source:
--   Gaussian Quantum Information, arXiv:1110.3234v1, PDF p. 9, §II.C.1 Eq.(45): physicality in Williamson coordinates

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P08

open scoped BigOperators ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

/-- PDF p.9, Eq.(45): uncertainty iff positive definiteness and a Williamson
form with every parameter at least one. The decomposition is constructed on the right. -/
theorem physicality_williamson (n : ℕ) (hn : 0 < n)
    (V : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ) (hVsym : V.transpose = V) :
    quantumCovariance V ↔
      V.PosDef ∧ ∃ nu : Fin n → ℝ, ∃ S : Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ,
        (∀ k, 1 ≤ nu k) ∧ isSymplectic S ∧
        V = S * williamsonDiagonal nu * S.transpose := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P08

end
