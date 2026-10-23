-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_qubitFaceGeometry
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.qubitFaceGeometry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:54:12.246135+00:00
-- url     : https://prove2.me/theorems/e1892b56-1869-4b3a-a2cc-c7a877c23224
-- title:
--   B.4: degradable edges, EB triangle and antidegradable disk
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   An edge joining distinct Pauli conjugations $\sigma_i,\sigma_j$ is the mixture $p\,\sigma_i\rho\sigma_i+(1-p)\sigma_j\rho\sigma_j$, $0\le p\le1$. Every edge channel is degradable and is antidegradable exactly at $p=1/2$. On the face $a_0=0$, write $p_k=a_k^2\ge0$, $\sum_{k=1}^3p_k=1$, so that $\lambda_k=2p_k-1$ and $\sum_k\lambda_k=-1$. Then
--   $$P_a\text{ is EB}\iff p_k\le\tfrac12\ \forall k,\qquad P_a\text{ is antidegradable}\iff\sum_{k=1}^3(\lambda_k+\tfrac13)^2\le\tfrac23.$$
--
--   Thus the EB set is the midpoint triangle, while the larger antidegradable set is the closed inscribed disk in the triangular face.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 34, B.4: degradable edges, EB triangle and antidegradable disk

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

/-- Appendix B.4, PDF pp.34–35 and Figure 1: all tetrahedron edges are
degradable (only their midpoints antidegradable); the face EB region is the
midpoint triangle and its antidegradable region is the closed inscribed disk. -/
theorem qubitFaceGeometry :
    (∀ i j : Fin 4, i ≠ j → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      let a : Fin 4 → ℝ := fun k =>
        if k=i then Real.sqrt p else if k=j then Real.sqrt (1-p) else 0
      (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap a) ∧ IsDegradable witness) ∧ ((∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap a) ∧ IsAntidegradable witness) ↔ p=1/2)) ∧
    (∀ p : Fin 3 → ℝ, (∀ k, 0 ≤ p k) → (∑ k, p k)=1 →
      let Phi := qubitPauliMap (faceAmplitudes p)
      let lam := pauliMultipliers (faceAmplitudes p)
      (∑ k, lam k) = -1 ∧
      (ChannelEB Phi ↔ ∀ k, p k ≤ 1/2) ∧
      ((∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness) ↔ (∑ k, (lam k+1/3)^2) ≤ (2/3 : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
