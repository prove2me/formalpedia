-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_replica_covariance_relabeling
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.replica_covariance_relabeling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:55:39.094984+00:00
-- url     : https://prove2.me/theorems/c9fd1062-a1a7-4550-8f90-54d088d623b9
-- title:
--   Covariance and relabeling of every replicated effect
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Suppose a feasible instrument of either timing is diagonal, covariant under $\overline U_A\otimes\overline U_B\otimes U_C$, and invariant under simultaneous relabeling of its three block indices. Let $T_\sigma|i\rangle=|\sigma(i)\rangle$. Then
--   $$G_{\sigma(i)\sigma(j)}^R(U)=(UT_\sigma)^{\otimes2}G_{ij}^R(I)(T_\sigma^\dagger U^\dagger)^{\otimes2}$$
--   for every orientation $U$, permutation $\sigma$, and pair $i,j$. This describes each replicated effect without any exchange-symmetry assumption.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 5, Remark 1: covariance and relabeling of replicated POVMs

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.5, Remark 1, Eq.(34): an identity for
individual replicas, with no exchange-symmetry hypothesis. -/
theorem replica_covariance_relabeling (d : ℕ) (hd : 2 ≤ d) (timing : Timing)
    (R : ReplicationChoiArray d) (hR : IsReplicationStrategy timing R) (hDiag : dephaseClassicalOutput R = R)
    (hCov : BlocksCommuteWithRotations (diagonalBlocks R)) (hRel : RelabelInvariant (diagonalBlocks R)) :
    ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ sigma : Equiv.Perm (Fin d), ∀ i j,
      let V := pairAction ((U : Op (Fin d)) * permutationMatrix sigma)
      replica R U (sigma i) (sigma j) = V * replica R 1 i j * V.conjTranspose := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
