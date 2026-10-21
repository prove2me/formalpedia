-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_corollary9_expansionSlice
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.corollary9_expansionSlice
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:50:33.244228+00:00
-- url     : https://prove2.me/theorems/4d9206e5-2126-4546-baa8-0e874763f91e
-- title:
--   Corollary 9
-- statement:
--   Consider the actual Appendix A.3 construction for an $n$-qubit $k$-local Hermitian $H$, where $n,k\ge1$, $c_e\ge1$, $1\le d_e\le n$, and $H$ has expansion $(c_e,d_e)$. The selected degree $a\in\{1,\ldots,k\}$ maximizes $\sum_{|P|=a}|\alpha_P|^{2d_e/(d_e+1)}$. Set $q=a-1$. For wire $i$ and axis $p\in\{X,Y,Z\}$, let $H_{a,i,p}$ be the weight-$a$ Pauli slice with $P_i=p$, with wire $i$ deleted. The first $q$ replicas are independent single-qubit Haar pure states $\rho_{s,j}$. The number $\beta_{i,p}$ is the signed uniform average in Eq.(A24), and the last replica at wire $i$ is the pure maximizer of $\sum_p\beta_{i,p}p$. A zero field is resolved by any pure maximizer. With all $a$ replicas, define
--   $$\rho(t;\rho_{\cdot,\cdot},\sigma)=\bigotimes_j\left[\frac I2+\frac ta\sum_{s=1}^a\sigma_s(\rho_{s,j}-I/2)\right].$$
--   Set $r=2d_e/(d_e+1)$, $F(b)=\sqrt{2b!}/(b^{b+3/2}6^{b/2})$, and $L_a=(\sum_{|P|=a}|\alpha_P|^r)^{1/r}$. Both inequalities hold:
--   $$\mathbb E_{\mathrm{Haar}}\mathbb E_\sigma|\operatorname{tr}(H_a\rho(1))|\ge\frac{F(a)}{c_e^{1/(2d_e)}}L_a\ge\frac{F(k)}{c_e^{1/(2d_e)}}L_a.$$
--   This records both the selected-slice and ambient-locality prefactors.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 29, Corollary 9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Corollary 9, paper p.29, A86-A87: both inequalities are retained. -/
theorem corollary9_expansionSlice (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1) :
    let mass := sliceMass (q + 1) (expansionExponent de) H
    let den := Real.rpow ce (1 / (2 * (de : ℝ)))
    sliceConstant (q + 1) / den * mass ≤ optimizedSliceMean (q := q) H ∧
      sliceConstant k / den * mass ≤ sliceConstant (q + 1) / den * mass := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
