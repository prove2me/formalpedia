-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_unitalQubitCriterion
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.unitalQubitCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:32:49.47098+00:00
-- url     : https://prove2.me/theorems/fdae612b-4ad1-4c89-801d-e99b159abe63
-- title:
--   Theorem 8
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\Psi$ be a unital qubit channel. Write $L_\lambda$ for the linear map fixing $I$ and sending $\sigma_k$ to $\lambda_k\sigma_k$. Then $\Psi$ is antidegradable exactly when it is unitarily equivalent on input and output to some $L_\lambda$ with $|\lambda_k|\le1$, both CP inequalities $(\lambda_i\pm\lambda_j)^2\le(1\pm\lambda_k)^2$ for distinct indices, and
--   $$\sum_{k=1}^3\left(1-|\lambda_k|+\sqrt{(1-|\lambda_k|)^2-(|\lambda_i|-|\lambda_j|)^2}\right)\ge2,$$
--   where $i,j$ are the other two indices in each summand.
--
--   Complete positivity remains a separate requirement; the square-root condition alone does not imply it.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 15, Theorem 8

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

/-- Theorem 8, PDF pp.15,37–38. Complete positivity is retained separately
from the square-root inequality, including all unitary changes of basis. -/
theorem unitalQubitCriterion (Phi : Superop Bool Bool)
    (hPhi : IsChannel Phi) (hunital : Phi 1 = 1) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = Phi ∧ IsAntidegradable witness) ↔ ∃ lam : Fin 3 → ℝ,
      RectangularUnitaryConjugate Phi (multiplierChannel lam) ∧ CPBounds lam ∧
      2 ≤ antiExpression lam := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
