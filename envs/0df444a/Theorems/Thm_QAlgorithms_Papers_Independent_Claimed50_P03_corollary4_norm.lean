-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_corollary4_norm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.corollary4_norm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:40:39.92299+00:00
-- url     : https://prove2.me/theorems/35b750db-d0ca-48f5-8531-2483bfeae9e9
-- title:
--   Corollary 4 (Norm inequality for bounded-degree local Hamiltonian)
-- statement:
--   Write $\mathcal P_n=\{I,X,Y,Z\}^{\otimes n}$ for phase-free Pauli words, $|P|$ for their nonidentity weight, and $\alpha_P=2^{-n}\operatorname{tr}(PH)$ for the real coefficients of a Hermitian $n$-qubit operator $H$. The norm $\|H\|$ is the spectral norm, and $\|H\|_{\mathrm{Pauli},p}=(\sum_{P\in\mathcal P_n}|\alpha_P|^p)^{1/p}$ includes the identity coefficient.
--
--   For integers $k,d\ge1$, set
--   $$C(k,d)=\frac{\sqrt{2k!}}{\sqrt d\,k^{k+5/2}(2\sqrt6+4\sqrt3)^k}.$$
--   A bounded-degree decomposition means a finite sum of Hermitian terms supported on at most $k$ wires each, with at most $d$ terms incident on any wire.For every $n\ge1$ and every Hermitian $H$ with such a decomposition,
--   $$\frac{C(k,d)}3\|H\|_{\mathrm{Pauli},1}\le\|H\|.$$
--   The bound controls the total Pauli coefficient mass independently of register size.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 8, Corollary 4 (Norm inequality for bounded-degree local Hamiltonian)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Corollary 4, paper p.8, Eq.22; exact C(k,d) is supplied on p.31, B12. -/
theorem corollary4_norm (n k d : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hdeg : HasBoundedDegree k d H) :
    degreeConstant k d / 3 * pauliNorm 1 H ≤ specNorm H := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
