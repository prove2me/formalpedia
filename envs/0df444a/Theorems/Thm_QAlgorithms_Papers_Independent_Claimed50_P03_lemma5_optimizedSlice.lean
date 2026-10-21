-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma5_optimizedSlice
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma5_optimizedSlice
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:48:03.554796+00:00
-- url     : https://prove2.me/theorems/7abd883e-8f45-4e95-b1f9-4a643ae69130
-- title:
--   Lemma 5 (Characterization of 𝜌(𝑡) for 𝑡 = 1)
-- statement:
--   Consider the actual Appendix A.3 construction for an $n$-qubit $k$-local Hermitian $H$, where $n,k\ge1$, $c_e\ge1$, $1\le d_e\le n$, and $H$ has expansion $(c_e,d_e)$. The selected degree $a\in\{1,\ldots,k\}$ maximizes $\sum_{|P|=a}|\alpha_P|^{2d_e/(d_e+1)}$. Set $q=a-1$. For wire $i$ and axis $p\in\{X,Y,Z\}$, let $H_{a,i,p}$ be the weight-$a$ Pauli slice with $P_i=p$, with wire $i$ deleted. The first $q$ replicas are independent single-qubit Haar pure states $\rho_{s,j}$. The number $\beta_{i,p}$ is the signed uniform average in Eq.(A24), and the last replica at wire $i$ is the pure maximizer of $\sum_p\beta_{i,p}p$. A zero field is resolved by any pure maximizer. With all $a$ replicas, define
--   $$\rho(t;\rho_{\cdot,\cdot},\sigma)=\bigotimes_j\left[\frac I2+\frac ta\sum_{s=1}^a\sigma_s(\rho_{s,j}-I/2)\right].$$
--   Let $H_a=\sum_{|P|=a}\alpha_PP$ and set
--   $$F(a)=\frac{\sqrt{2a!}}{a^{a+3/2}6^{a/2}}.$$
--   The construction satisfies
--   $$\mathbb E_{\mathrm{Haar}}\mathbb E_\sigma|\operatorname{tr}(H_a\rho(1))|\ge F(a)\sum_{i,p}\sqrt{\sum_{|P|=a,\,P_i=p}\alpha_P^2}.$$
--   The sum over wire and axis is outside the square root. This is a mean absolute energy guarantee for the constructed path.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 27, Lemma 5 (Characterization of 𝜌(𝑡) for 𝑡 = 1)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 5, paper p.27, A60: expectation of an absolute value, for the
constructed local maximizers; not an absolute value of the mean. -/
theorem lemma5_optimizedSlice (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1) :
    sliceConstant (q + 1) * sliceInfluence (q + 1) H ≤ optimizedSliceMean (q := q) H := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
