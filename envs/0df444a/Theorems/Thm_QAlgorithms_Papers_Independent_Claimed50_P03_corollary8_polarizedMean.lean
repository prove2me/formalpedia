-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_corollary8_polarizedMean
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.corollary8_polarizedMean
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:47:32.506119+00:00
-- url     : https://prove2.me/theorems/18c8580d-9b35-44c2-b507-98690f373fe0
-- title:
--   Corollary 8
-- statement:
--   Consider the actual Appendix A.3 construction for an $n$-qubit $k$-local Hermitian $H$, where $n,k\ge1$, $c_e\ge1$, $1\le d_e\le n$, and $H$ has expansion $(c_e,d_e)$. The selected degree $a\in\{1,\ldots,k\}$ maximizes $\sum_{|P|=a}|\alpha_P|^{2d_e/(d_e+1)}$. Set $q=a-1$. For wire $i$ and axis $p\in\{X,Y,Z\}$, let $H_{a,i,p}$ be the weight-$a$ Pauli slice with $P_i=p$, with wire $i$ deleted. The first $q$ replicas are independent single-qubit Haar pure states $\rho_{s,j}$. The number $\beta_{i,p}$ is the signed uniform average in Eq.(A24), and the last replica at wire $i$ is the pure maximizer of $\sum_p\beta_{i,p}p$. A zero field is resolved by any pure maximizer. With all $a$ replicas, define
--   $$\rho(t;\rho_{\cdot,\cdot},\sigma)=\bigotimes_j\left[\frac I2+\frac ta\sum_{s=1}^a\sigma_s(\rho_{s,j}-I/2)\right].$$
--   For each $i,p$,
--   $$\mathbb E\left|\operatorname{tr}\!\left(\operatorname{pol}(H_{a,i,p})\bigotimes_{s\le q,\,j\ne i}\rho_{s,j}\right)\right|\ge6^{-q/2}\sqrt{\frac{\operatorname{tr}(H_{a,i,p}^2)}{2^n q!}}.$$
--   Here $H_{a,i,p}$ acts on $n-1$ wires, while the displayed denominator deliberately remains $2^n$, as printed. This independent claim gives a lower bound on the polarized mean magnitude.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 26, Corollary 8

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Corollary 8, paper p.26, A59. H_{q+1,i,p} really acts on n-1 wires;
the printed denominator 2^n is retained, giving a weaker bound than 2^(n-1).
The printed repeated-i tensor index is read as j≠i, per A23.
This is audited independently of the defective printed Lemma 4. -/
theorem corollary8_polarizedMean (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1) (i : Fin n) (p : Fin 3) :
    (1 / Real.sqrt 6) ^ q *
      Real.sqrt (((deletedSlice (q + 1) H i p * deletedSlice (q + 1) H i p).trace.re) /
        ((2 : ℝ) ^ n * (Nat.factorial q : ℝ))) ≤
      ∫ u, |effectProb (polarization q (deletedSlice (q + 1) H i p))
        (namedWireTensor (fun sj : Fin q × {j : Fin n // j ≠ i} => haarQubit (u (sj.1, sj.2.val))))|
        ∂haarProductLaw (Fin q × Fin n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
