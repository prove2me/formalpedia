-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_symmetric_conversion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.symmetric_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:59:57.018903+00:00
-- url     : https://prove2.me/theorems/b18ae3af-9e26-4b42-8131-b68af23d20c6
-- title:
--   §2, Eqs. (12)–(14): explicit symmetric two-mode CM/EM transform
-- statement:
--   Let the physical covariance of a symmetric two-mode Gaussian state be
--   $$\alpha_q=\tfrac12\begin{pmatrix}m&k_q\\k_q&m\end{pmatrix},\qquad \alpha_p=\tfrac12\begin{pmatrix}m&-k_p\\-k_p&m\end{pmatrix}.$$
--   Put $s_1=((m+k_q)/(m-k_p))^{1/4}$ and $s_2=((m-k_q)/(m+k_p))^{1/4}$, and set $S_q=2^{-1/2}\begin{pmatrix}s_1&s_2\\s_1&-s_2\end{pmatrix}$, $S=S_q\oplus S_q^{-T}$. All four quantities $m\pm k_q,m\pm k_p$ are positive, $S$ is symplectic, and
--   $$\alpha=S\operatorname{diag}(\gamma_A,\gamma_B,\gamma_A,\gamma_B)S^T,\quad \gamma_A=\tfrac12\sqrt{(m+k_q)(m-k_p)},\quad \gamma_B=\tfrac12\sqrt{(m-k_q)(m+k_p)}.$$
--   Both eigenvalues are at least $1/2$. If they are strictly larger, the finite exponential matrix is $S^{-T}\operatorname{diag}(m_A,m_B,m_A,m_B)S^{-1}$, with $m_j=\ln((2\gamma_j+1)/(2\gamma_j-1))$. This gives an explicit conversion without excluding pure modes from the diagonalization. The finite exponential matrix refers to the actual normalized Gibbs density: after a bounded unitary implementing the stated symplectic transformation, its number-basis weights are $\prod_j(1-e^{-m_j})e^{-m_j n_j}$. This operator meaning is part of the conclusion, alongside the covariance normal form.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 3, §2, Eqs. (12)–(14): explicit symmetric two-mode CM/EM transform

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

/-- Chen, PDF p.3, (12)–(14): explicit symmetric two-mode diagonalization.
Physicality guards denominators and fourth roots. No finite EM is assigned to a
pure mode; that extra clause requires both normal eigenvalues to exceed 1/2. -/
theorem symmetric_conversion (m kq kp : ℝ)
    (hphysical : IsPhysicalCovariance (symmetricCM m kq kp)) :
    let S := symplecticLift (symmetricSq m kq kp)
    let g := symmetricGammas m kq kp
    0 < m + kq ∧ 0 < m - kq ∧ 0 < m + kp ∧ 0 < m - kp ∧
      IsSymplecticMatrix S ∧ (∀ j, 1 / 2 ≤ g j) ∧
      symmetricCM m kq kp = S * normalDiagonal g * S.transpose ∧
      ((∀ j, 1 / 2 < g j) → GaussianEM (symmetricCM m kq kp) (emFrom S g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
