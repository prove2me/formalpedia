-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_relabel_transport
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.relabel_transport
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:55:00.46141+00:00
-- url     : https://prove2.me/theorems/47a0ff2f-894a-44b0-b0bc-45c9609f8c01
-- title:
--   Relabel averaging after covariance
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Suppose $R$ is diagonal on $D$, feasible for either timing, and its blocks $B_{ij,k}$ commute with every $V(U)=\overline U_A\otimes\overline U_B\otimes U_C$. Let $S_d$ be the permutation group of the labels and put
--   $$\widehat B_{ij,k}=\frac1{d!}\sum_{\sigma\in S_d}B_{\sigma(i)\sigma(j),\sigma(k)},\qquad\widehat R_{ij}=\sum_k\widehat B_{ij,k}\otimes|k\rangle\langle k|_D.$$
--   Then $\widehat R$ is feasible for the same timing, diagonal and covariant, with
--   $$\widehat B_{ij,k}=\widehat B_{\sigma(i)\sigma(j),\sigma(k)},\qquad F(\widehat R)=F(R).$$
--   This transport reduces dependence on the outcome labels to their equality patterns. Covariance is required for this index-only form of the permutation average.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 5, Lemma 4 (Relabeling symmetry)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.5, Lemma 4 and Eq.(32): the index-only
average is applied after covariance, when permutation conjugations disappear. -/
theorem relabel_transport (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) (hDiag : dephaseClassicalOutput R = R)
    (hCov : BlocksCommuteWithRotations (diagonalBlocks R)) :
    IsReplicationStrategy timing (relabel R) ∧ BlocksCommuteWithRotations (diagonalBlocks (relabel R)) ∧
    RelabelInvariant (diagonalBlocks (relabel R)) ∧
    dephaseClassicalOutput (relabel R) = relabel R ∧ haarReplicationScore (relabel R) = haarReplicationScore R := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
