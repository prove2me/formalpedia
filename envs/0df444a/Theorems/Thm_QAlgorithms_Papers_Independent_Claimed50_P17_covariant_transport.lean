-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_covariant_transport
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.covariant_transport
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:54:17.66434+00:00
-- url     : https://prove2.me/theorems/883a6750-8f08-47f1-af6c-fa9a0ee13e36
-- title:
--   Haar twirling preserves the score and yields covariance
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Let $B_{ij,k}=\langle k|_D R_{ij}|k\rangle_D$ and $V(U)=\overline U_A\otimes\overline U_B\otimes U_C$. Define
--   $$\widetilde B_{ij,k}=\int V(U)B_{ij,k}V(U)^\dagger\,dU,\qquad\widetilde R_{ij}=\sum_k\widetilde B_{ij,k}\otimes|k\rangle\langle k|_D.$$
--   For every feasible $R$ of either timing, these integrals and its score integral are integrable, $\widetilde R$ is feasible for the same timing, and
--   $$[\widetilde B_{ij,k},V(U)]=0\quad\text{for every }U,i,j,k,\qquad F(\widetilde R)=F(R).$$
--   The output remains diagonal on $D$. This supplies a constructive covariant optimum while asserting preservation of the average score.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 4, Lemma 3 (Restriction to covariant networks)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF pp.4-5, Lemma 3 and Eq.(29): twirling
preserves feasibility and Haar score, and yields commuting blocks.
Integrability is a conclusion, not an extra restriction on instruments.
For the finite ABC matrix, integrability is stated for every complex entry. -/
theorem covariant_transport (d : ℕ) (hd : 2 ≤ d) (timing : Timing) (R : ReplicationChoiArray d)
    (hR : IsReplicationStrategy timing R) :
    (∀ i j k, ∀ x y : ABC d,
      Integrable (fun U : (Matrix.unitaryGroup (Fin d) ℂ) =>
        (representation U * diagonalBlocks R i j k * (representation U).conjTranspose) x y)
        (QAlgorithms.Schur.unitaryHaar d)) ∧
    Integrable (scoreIntegrand R) (QAlgorithms.Schur.unitaryHaar d) ∧
    IsReplicationStrategy timing (twirl R) ∧ BlocksCommuteWithRotations (diagonalBlocks (twirl R)) ∧
    twirl R = dephaseClassicalOutput (twirl R) ∧ haarReplicationScore (twirl R) = haarReplicationScore R := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
