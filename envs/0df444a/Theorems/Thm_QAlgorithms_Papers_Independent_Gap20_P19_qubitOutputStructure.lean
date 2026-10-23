-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_qubitOutputStructure
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.qubitOutputStructure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:41:28.292113+00:00
-- url     : https://prove2.me/theorems/10a777f1-984c-4350-aaf9-78a85cfcd326
-- title:
--   Theorem 4: complete degradable qubit-output structure (original paper seed)
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\Phi:M_{d_A}\to M_2$ be degradable. Then
--   $$r(\Phi)\le2,\qquad d_A\le3.$$
--   If $d_A=3$, independent unitary conjugations on input and output turn $\Phi$ into $Q(\rho)=A_0\rho A_0^\dagger+A_1\rho A_1^\dagger$, where
--   $$A_0=\begin{pmatrix}1&0&0\\0&1/\sqrt2&0\end{pmatrix},\qquad A_1=\begin{pmatrix}0&1/\sqrt2&0\\0&0&1\end{pmatrix}.$$
--   The displayed $Q$ is both degradable and antidegradable.
--
--   This is the precise complete qubit-output result advertised by the paper's abstract; the original seed node is preserved.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 12, Theorem 4: complete degradable qubit-output structure (original paper seed)

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

/-- Theorem 4, PDF pp.12–14: both dimension bounds, canonical uniqueness,
and both classes for the explicit qutrit-to-qubit channel. -/
theorem qubitOutputStructure [Nonempty A] (Phi : Superop A Bool)
    (hPhi : IsChannel Phi) (hdeg : (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsDegradable witness)) :
    (choi Phi).rank ≤ 2 ∧ Fintype.card A ≤ 3 ∧
    (Fintype.card A = 3 → ∃ e : A ≃ Fin 3,
      RectangularUnitaryConjugate (fun rho => Phi (fun a b => rho (e a) (e b))) qutritCanonical) ∧
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = qutritCanonical ∧ IsDegradable witness) ∧ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = qutritCanonical ∧ IsAntidegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
