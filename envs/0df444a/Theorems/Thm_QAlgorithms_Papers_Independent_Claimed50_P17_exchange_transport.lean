-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_exchange_transport
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.exchange_transport
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:56:48.088549+00:00
-- url     : https://prove2.me/theorems/502b5edc-3038-469e-9c17-b00646766a25
-- title:
--   Operational averaging under exchange of the two replicas
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Let $\mathcal X(R)$ exchange wires $A,B$ and labels $i,j$, keeping $C,D$ fixed. Define $\overline R=(R+\mathcal X(R))/2$. For every feasible instrument of either timing,
--   $$\overline R\text{ is feasible},\qquad\mathcal X(\overline R)=\overline R,\qquad F(\overline R)=F(R).$$
--   If $R$ was diagonal, covariant, or simultaneously relabel invariant, the corresponding property is preserved by this average. This supplies the exchange-symmetric choice used in the optimization.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 6, Lemma 5: exchange symmetry

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.6, Lemma 5: the actual operational
averaging map, preserving the earlier reductions as well as feasibility and score. -/
theorem exchange_transport (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) :
    IsReplicationStrategy timing (symmetrize R) ∧ exchange (symmetrize R) = symmetrize R ∧
    haarReplicationScore (symmetrize R) = haarReplicationScore R ∧
    (dephaseClassicalOutput R = R → dephaseClassicalOutput (symmetrize R) = symmetrize R) ∧
    (BlocksCommuteWithRotations (diagonalBlocks R) → BlocksCommuteWithRotations (diagonalBlocks (symmetrize R))) ∧
    (RelabelInvariant (diagonalBlocks R) → RelabelInvariant (diagonalBlocks (symmetrize R))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
