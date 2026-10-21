-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_cloning_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.cloning_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:51:28.241598+00:00
-- url     : https://prove2.me/theorems/487cfb4d-01e7-44e7-a2ef-345106908db3
-- title:
--   Optimal one-to-two measurement cloning fidelity
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   There is a feasible cloning instrument $R_\star$ attaining the full operational maximum:
--   $$F(R_\star)=\frac4{3d},\qquad F(R)\le\frac4{3d}\quad\text{for every feasible cloning instrument }R.$$
--   This is an attained optimum over all one-use instruments, including those without symmetry restrictions. It does not identify the defective printed Eq.(62) blocks as maximizers.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 7, §V, Eq.(61): optimal one-to-two cloning fidelity (seed announced in abstract)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.7, Eq.(61): attained optimal score over the full
operational cloning domain. The defective printed Eq.(62) attainers are not assumed. -/
theorem cloning_optimum (d : ℕ) (hd : 2 ≤ d) :
    ∃ R : ReplicationChoiArray d, IsReplicationStrategy .cloning R ∧ haarReplicationScore R = 4/(3*(d : ℝ)) ∧
      ∀ T : ReplicationChoiArray d, IsReplicationStrategy .cloning T → haarReplicationScore T ≤ 4/(3*(d : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
