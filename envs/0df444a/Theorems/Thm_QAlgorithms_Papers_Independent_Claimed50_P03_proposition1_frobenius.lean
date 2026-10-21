-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_proposition1_frobenius
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.proposition1_frobenius
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:51:58.893769+00:00
-- url     : https://prove2.me/theorems/c3289fc2-5cbe-427a-bf7f-e5a9ea9d8ef2
-- title:
--   Proposition 1 (Frobenius norm)
-- statement:
--   Write $\mathcal P_n=\{I,X,Y,Z\}^{\otimes n}$ for phase-free Pauli words, $|P|$ for their nonidentity weight, and $\alpha_P=2^{-n}\operatorname{tr}(PH)$ for the real coefficients of a Hermitian $n$-qubit operator $H$. The norm $\|H\|$ is the spectral norm, and $\|H\|_{\mathrm{Pauli},p}=(\sum_{P\in\mathcal P_n}|\alpha_P|^p)^{1/p}$ includes the identity coefficient.
--
--   For every Hermitian $H$, including a scalar zero-wire operator,
--   $$\frac{\|H\|_F}{\sqrt{2^n}}=\|H\|_{\mathrm{Pauli},2}\le\|H\|.$$
--   Here $\|H\|_F=(\sum_{x,y}|H_{xy}|^2)^{1/2}$ is the Frobenius norm. This fixes the normalization relating coefficient and operator scales.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 30, Proposition 1 (Frobenius norm)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Proposition 1, paper p.30, B2: explicitly named Frobenius and spectral norms. -/
theorem proposition1_frobenius (n : ℕ) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) :
    frobNorm H / Real.sqrt ((2 : ℝ) ^ n) = pauliNorm 2 H ∧
      pauliNorm 2 H ≤ specNorm H := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
