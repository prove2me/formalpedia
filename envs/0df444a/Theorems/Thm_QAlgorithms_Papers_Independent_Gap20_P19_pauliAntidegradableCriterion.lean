-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_pauliAntidegradableCriterion
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.pauliAntidegradableCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:32:01.301236+00:00
-- url     : https://prove2.me/theorems/7481be9a-648b-4855-aab5-a0673eebed0a
-- title:
--   Theorem 7
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   Let $\sigma_0=I$ and $\sigma_1,\sigma_2,\sigma_3=X,Y,Z$. For real amplitudes $a_k\ge0$ with $\sum_{k=0}^3a_k^2=1$, put $P_a(\rho)=\sum_{k=0}^3 a_k^2\sigma_k\rho\sigma_k$ and $\lambda_k=a_0^2+a_k^2-a_i^2-a_j^2$, where $\{i,j,k\}=\{1,2,3\}$.
--
--   Assume additionally $a_0\ge a_k$ for every $k$. Then
--   $$P_a\text{ is antidegradable}\iff a_1^2+a_2^2+a_3^2+a_1a_2+a_1a_3+a_2a_3\ge\tfrac12.$$
--
--   This is the amplitude form of the unital-qubit criterion.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 15, Theorem 7

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

/-- Theorem 7, PDF p.15. a_0 is the largest nonnegative Kraus amplitude.
The symmetric expression uses precisely the indices 1,2,3. -/
theorem pauliAntidegradableCriterion (a : Fin 4 → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hmax : ∀ k, a k ≤ a 0) (hnorm : ∑ k, a k^2 = 1) :
    (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (qubitPauliMap a) ∧ IsAntidegradable witness) ↔
      (1/2 : ℝ) ≤ a 1^2+a 2^2+a 3^2+a 1*a 2+a 1*a 3+a 2*a 3 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
