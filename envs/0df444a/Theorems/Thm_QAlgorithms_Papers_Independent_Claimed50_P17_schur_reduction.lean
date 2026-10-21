-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_schur_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.schur_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:56:14.608202+00:00
-- url     : https://prove2.me/theorems/c6d574e2-dc59-4428-b263-40d94f7f50ca
-- title:
--   Outcome classes and concrete positive Schur blocks
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   For positive diagonal blocks $B_{ij,k}$ that are covariant and invariant under simultaneous relabeling, the equality patterns of $(i,j,k)$ are precisely their permutation orbits. Define the two embeddings $J_\pm:\mathbb C^d\to A\otimes B\otimes C$ by
--   $$J_\pm|m\rangle=\frac{\sum_a|a,m,a\rangle\pm\sum_a|m,a,a\rangle}{\sqrt{2(d\pm1)}}.$$
--   They obey $J_a^\dagger J_b=\delta_{ab}I$ and $V(U)J_a=J_a\overline U$, where $V(U)=\overline U_A\otimes\overline U_B\otimes U_C$. Put $P^\beta=P^+_{AB}\otimes I_C-J_+J_+^\dagger$ and $P^\gamma=P^-_{AB}\otimes I_C-J_-J_-^\dagger$, where $P^\pm_{AB}$ project onto the symmetric and antisymmetric pair spaces. There are positive multiplicity blocks with
--   $$B_{ij,k}=\sum_{a,b\in\{+,-\}}(r_\ell^\alpha)_{ab}J_aJ_b^\dagger+r_\ell^\beta P^\beta+r_\ell^\gamma P^\gamma,\qquad\ell=[ij,k].$$
--   These residual operators are positive orthogonal projectors of dimensions $d(d-1)(d+2)/2$ and $d(d+1)(d-2)/2$, respectively. Beta and gamma coefficients are nonnegative scalars, with gamma omitted at $d=2$. Here $n_\ell$ is the cardinality of the outcome class $\ell$. The scaled blocks $s_\ell^\nu=(n_\ell/d)r_\ell^\nu$ reconstruct the full instrument, and its score equals the sum of the three sector scores calculated by the actual contractions $d^{-2}\sum_{ijk}\langle ijk|B_{ij,k}^\nu|ijk\rangle$.
--
--   This concrete representation supports operational normalization and optimization without the source's inconsistent numerical coefficient table.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 5, §IV, Eqs.(35)–(47): outcome classes and concrete invariant block representation

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF pp.5-6, Eqs.(35)-(47): outcome orbits,
concrete orthogonal alpha embeddings, positive Schur blocks and the contraction score.
Tensor order is P_AB tensor I_C. The erroneous numerical Eq.(48) is not used. -/
theorem schur_reduction (d : ℕ) (hd : 2 ≤ d) :
    (∀ i j k i2 j2 k2 : Fin d, outcomeClass i j k = outcomeClass i2 j2 k2 ↔
      ∃ sigma : Equiv.Perm (Fin d), sigma i = i2 ∧ sigma j = j2 ∧ sigma k = k2) ∧
    (∀ a c : Fin 2, (alphaEmbedding d a).conjTranspose * alphaEmbedding d c =
      if a = c then 1 else 0) ∧
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ a : Fin 2,
      representation U * alphaEmbedding d a =
        alphaEmbedding d a * ((U : Op (Fin d)).map conj)) ∧
    (∀ a : Fin 2, (residualProjector d a).PosSemidef ∧
      residualProjector d a * residualProjector d a = residualProjector d a ∧
      (Matrix.trace (residualProjector d a)).re =
        replicationSectorDimension d (if a = 0 then 1 else 2)) ∧
    (∀ B : DiagonalInstrument d, (∀ i j k, (B i j k).PosSemidef) →
      BlocksCommuteWithRotations B → RelabelInvariant B →
      ∃ b : BlockArray, BlockShape d b ∧ liftDiagonal B = expandBlocks d b ∧
        haarReplicationScore (liftDiagonal B) = ∑ v : Fin 3, sectorScore d b v) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
