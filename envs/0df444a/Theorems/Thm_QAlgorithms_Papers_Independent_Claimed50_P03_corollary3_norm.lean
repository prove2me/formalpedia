-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_corollary3_norm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.corollary3_norm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:39:30.955879+00:00
-- url     : https://prove2.me/theorems/d07d5f77-f7bb-4f39-b914-d2e527e3aecf
-- title:
--   Corollary 3 (Norm inequality for general 𝑘-local Hamiltonian)
-- statement:
--   Write $\mathcal P_n=\{I,X,Y,Z\}^{\otimes n}$ for phase-free Pauli words, $|P|$ for their nonidentity weight, and $\alpha_P=2^{-n}\operatorname{tr}(PH)$ for the real coefficients of a Hermitian $n$-qubit operator $H$. The norm $\|H\|$ is the spectral norm, and $\|H\|_{\mathrm{Pauli},p}=(\sum_{P\in\mathcal P_n}|\alpha_P|^p)^{1/p}$ includes the identity coefficient.
--
--   For an integer $k\ge1$, set $r_k=2k/(k+1)$ and
--   $$C(k)=\frac{\sqrt{2k!}}{2k^{k+3/2+(k+1)/(2k)}(\sqrt6+2\sqrt3)^k}.$$
--   For every $n\ge1$ and every $k$-local Hermitian $H$,
--   $$\frac{C(k)}3\|H\|_{\mathrm{Pauli},r_k}\le\|H\|.$$
--   This controls a coefficient norm with exponent below two by the operator norm.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 7, Corollary 3 (Norm inequality for general 𝑘-local Hamiltonian)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Corollary 3, paper p.7, Eq.21; exact C(k) is supplied on p.31, B11. -/
theorem corollary3_norm (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H) :
    localityConstant k / 3 * pauliNorm (expansionExponent k) H ≤ specNorm H := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
