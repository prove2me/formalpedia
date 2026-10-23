-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_pseudoDiagonalAndEB
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.pseudoDiagonalAndEB
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:34:50.576167+00:00
-- url     : https://prove2.me/theorems/5e40043d-9504-4f0f-a9a4-bbc7c56ff98c
-- title:
--   Theorem 11
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   A pseudo-diagonal channel has, in an orthonormal output basis and for arbitrary input vectors $w_j$, the form $\Phi(\rho)_{jk}=c_{jk}\langle w_j|\rho|w_k\rangle$, where $c$ is positive semidefinite and the full map is trace preserving. Every such channel is degradable. Equivalently, every entanglement-breaking channel is antidegradable:
--   $$\Phi\text{ pseudo-diagonal}\Longrightarrow\Phi\text{ degradable},\qquad \Phi\text{ entanglement breaking}\Longrightarrow\Phi\text{ antidegradable}.$$
--
--   The vectors need not be orthogonal or separately normalized; the output basis may be changed unitarily.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 19, Theorem 11

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

/-- Theorem 11, PDF p.19. Both formulations are retained, on arbitrary
nonzero finite systems. No individual frame-vector normalization is required. -/
theorem pseudoDiagonalAndEB [Nonempty A] [Nonempty B] :
    (∀ Phi : Superop A B, IsChannel Phi → PseudoDiagonal Phi → (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness)) ∧
    (∀ Phi : Superop A B, IsChannel Phi → ChannelEB Phi → (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
