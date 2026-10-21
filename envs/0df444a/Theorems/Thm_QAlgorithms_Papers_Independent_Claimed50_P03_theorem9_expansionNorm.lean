-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_theorem9_expansionNorm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.theorem9_expansionNorm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:52:32.674502+00:00
-- url     : https://prove2.me/theorems/dacfdce6-9899-4c84-8e03-adaeb910f6cf
-- title:
--   Theorem 9 (Norm inequality from Theorem 5)
-- statement:
--   Write $\mathcal P_n=\{I,X,Y,Z\}^{\otimes n}$ for phase-free Pauli words, $|P|$ for their nonidentity weight, and $\alpha_P=2^{-n}\operatorname{tr}(PH)$ for the real coefficients of a Hermitian $n$-qubit operator $H$. The norm $\|H\|$ is the spectral norm, and $\|H\|_{\mathrm{Pauli},p}=(\sum_{P\in\mathcal P_n}|\alpha_P|^p)^{1/p}$ includes the identity coefficient.
--
--   For an $n$-qubit Hermitian operator $H$ with real Pauli coefficients $\alpha_P$, write $\operatorname{supp}P$ for its nonidentity wires. The expansion property $(c_e,d_e)$ means that for each set $S$ of $d_e$ wires,
--   $$\#\{P:\alpha_P\ne0,\ S\subseteq\operatorname{supp}P\ \text{or}\ \operatorname{supp}P\subseteq S\}\le c_e.$$
--   The identity term is included in this count.
--
--   Assume $n,k\ge1$, $c_e\ge1$, $1\le d_e\le n$, and $H$ is $k$-local. Set $r=2d_e/(d_e+1)$ and
--   $$C(c_e,d_e,k)=\frac{\sqrt{2k!}}{c_e^{1/(2d_e)}k^{k+3/2+1/r}(\sqrt6+2\sqrt3)^k}.$$
--   Then
--   $$\frac{C(c_e,d_e,k)}3\|H\|_{\mathrm{Pauli},r}\le\|H\|.$$
--   The full coefficient norm includes $\alpha_I$. This norm consequence uses an expected absolute deviation and does not require repairing the optimization headlines' output-law claim.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 31, Theorem 9 (Norm inequality from Theorem 5)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Theorem 9, paper p.31, B4: identity coefficient included, exact A5 constant. -/
theorem theorem9_expansionNorm (n k de : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de) :
    expansionConstant ce de k / 3 * pauliNorm (expansionExponent de) H ≤ specNorm H := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
