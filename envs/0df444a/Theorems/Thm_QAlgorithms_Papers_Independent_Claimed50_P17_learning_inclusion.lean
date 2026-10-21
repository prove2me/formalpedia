-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_learning_inclusion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.learning_inclusion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:53:01.195562+00:00
-- url     : https://prove2.me/theorems/0f07979f-0004-48ee-9d9f-bb510f0d2055
-- title:
--   Learning embeds into cloning with identical replicas
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Every learning instrument $R$ is a cloning instrument under the identity embedding $\iota$, using $S_{ABC}=I_{AB}\otimes\rho_C$. Moreover,
--   $$G_{ij}^{\iota(R)}(U)=G_{ij}^R(U)\quad\text{for all }U,i,j,\qquad F(\iota(R))=F(R).$$
--   Consequently the supremum learning score is no larger than the supremum cloning score. The two score sets here retain their operational feasibility constraints. This inclusion accounts for the timing restriction on learning.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 2, §I: learning is a restricted cloning strategy

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.2 and Eq.(18)-(19): learning embeds by
S_ABC=I_AB tensor rho_C. Every replica is preserved, hence so is its score. -/
theorem learning_inclusion (d : ℕ) (hd : 2 ≤ d) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy .learning R) :
    IsReplicationStrategy .cloning (learningToCloning R) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j, replica (learningToCloning R) U i j = replica R U i j) ∧
    haarReplicationScore (learningToCloning R) = haarReplicationScore R ∧
    sSup (scoreValues d .learning) ≤ sSup (scoreValues d .cloning) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
