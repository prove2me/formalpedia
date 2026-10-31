-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P46_qp_conversion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P46.qp_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:59:10.739137+00:00
-- url     : https://prove2.me/theorems/7f2e4b2a-4d5f-4937-8146-3366d317aed8
-- title:
--   §2, Eqs. (7)–(11),(14): q–p-decorrelated CM to EM
-- statement:
--   Let $\alpha=\alpha_q\oplus\alpha_p$ be a physical real symmetric covariance for a positive finite number of modes, in grouped coordinates with vacuum covariance $I/2$. There are real vectors $C_j$, normal eigenvalues $\gamma_j\ge\tfrac12$, and an invertible matrix $S_q$ such that
--   $$\alpha_p\alpha_q C_j=\gamma_j^2 C_j,\qquad C_i^T\alpha_q C_j=\delta_{ij}\gamma_j,\qquad S_q=\alpha_q C\operatorname{diag}(\gamma_j^{-1}),\quad S_q^{-T}=C.$$
--   Consequently $S=S_q\oplus S_q^{-T}$ is symplectic and $\alpha=S\operatorname{diag}(\gamma,\gamma)S^T$. If all $\gamma_j>\tfrac12$, its finite exponential matrix is $M=S^{-T}\operatorname{diag}(m,m)S^{-1}$, where $m_j=\ln((2\gamma_j+1)/(2\gamma_j-1))$. Repeated eigenvalues require an orthogonal choice within their eigenspaces, and eigenvector signs do not matter. This constructs the conversion from the covariance rather than assuming a diagonalizer. The finite exponential matrix refers to the actual normalized Gibbs density: after a bounded unitary implementing the stated symplectic transformation, its number-basis weights are $\prod_j(1-e^{-m_j})e^{-m_j n_j}$. This operator meaning is part of the conclusion, alongside the covariance normal form.
-- source:
--   Gaussian relative entropy of entanglement, arXiv:quant-ph/0402109v3, PDF p. 3, §2, Eqs. (7)–(11),(14): q–p-decorrelated CM to EM

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

/-- Chen, PDF pp.2–3, (7)–(11),(14): construct S from a real q-orthogonal
eigenbasis of p*q, including repeated eigenvalues. Printed: choose c_jj>0.
Changed: leave signs free and choose a q-orthogonal basis within each repeated
eigenspace. Why: a designated coordinate may vanish, and sign does not affect
the constructed covariance or EM. Diagonalization includes pure modes; the conditional finite-EM clause does not. -/
theorem qp_conversion {I : Type} [Fintype I] [Nonempty I]
    (q p : Matrix I I ℝ) (hphysical : IsPhysicalCovariance (Matrix.fromBlocks q 0 0 p)) :
    ∃ (g : I → ℝ) (C Sq : Matrix I I ℝ),
      (∀ j, 1 / 2 ≤ g j) ∧
      (∀ j k, ∑ l, (p * q) k l * C l j = (g j) ^ 2 * C k j) ∧
      (∀ i j, (∑ k, ∑ l, C k i * q k l * C l j) =
        if i = j then g j else 0) ∧
      Sq = q * C * Matrix.diagonal (fun j => (g j)⁻¹) ∧
      Sq.transpose⁻¹ = C ∧
      let S := Matrix.fromBlocks Sq 0 0 Sq.transpose⁻¹
      IsSymplecticMatrix S ∧
        Matrix.fromBlocks q 0 0 p = S * normalDiagonal g * S.transpose ∧
        ((∀ j, 1 / 2 < g j) →
          GaussianEM (Matrix.fromBlocks q 0 0 p)
            (S.transpose⁻¹ * normalDiagonal (modeEM ∘ g) * S⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P46

end
