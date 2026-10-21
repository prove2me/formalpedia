-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_diagonal_transport
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.diagonal_transport
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:53:43.494778+00:00
-- url     : https://prove2.me/theorems/c986d672-d3d9-475e-bb53-969ad1428bfb
-- title:
--   Dephasing preserves feasibility and every replica
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   For either timing and every feasible instrument $R$, define $B_{ij,k}=\langle k|_D R_{ij}|k\rangle_D$ and
--   $$\mathcal D(R)_{ij}=\sum_k B_{ij,k}\otimes|k\rangle\langle k|_D.$$
--   Then $B_{ij,k}\succeq0$, $\mathcal D(R)$ is feasible for the same timing, and
--   $$G_{ij}^{\mathcal D(R)}(U)=G_{ij}^R(U)\quad\text{for every }U,i,j,\qquad F(\mathcal D(R))=F(R).$$
--   Thus an optimal instrument can be chosen diagonal on the classical output wire. The transport applies without an optimality hypothesis.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 4, Lemma 2 (Restriction to diagonal network)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.4, Lemma 2 and Eq.(25): the explicit diagonal
transport works for every feasible input and preserves each replica pointwise. -/
theorem diagonal_transport (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) :
    IsReplicationStrategy timing (dephaseClassicalOutput R) ∧
    (∀ i j k, (diagonalBlocks R i j k).PosSemidef) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j, replica (dephaseClassicalOutput R) U i j = replica R U i j) ∧
    haarReplicationScore (dephaseClassicalOutput R) = haarReplicationScore R := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
