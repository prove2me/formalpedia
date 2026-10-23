-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_noncommutingWeylObstruction
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.noncommutingWeylObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:37:24.627247+00:00
-- url     : https://prove2.me/theorems/6c3a0c8c-4734-450f-bf21-6709270f9d20
-- title:
--   Corollary 14
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   For an integer $d\ge1$, let $V_{j,k}=X^jZ^k$ with labels in $\mathbb Z_d^2$, forward cyclic shift $X$ and positive-phase clock $Z$. Let $a_m\ge0$, $\sum_m a_m=1$, and $P_a(\rho)=\sum_m a_mV_m\rho V_m^\dagger$. These $a_m$ are probabilities.
--
--   Retain the standing hypothesis $a_{0,0}\ne0$. If $a_l\ne0$, $a_k\ne0$, and $V_lV_k\ne V_kV_l$, then
--   $$P_a\text{ is not degradable}.$$
--
--   Identity support is essential: without it, a qubit mixture of $X$ and $Z$ contradicts this assertion.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 22, Corollary 14

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

/-- Corollary 14, PDF pp.21–22: standing a_0≠0 is retained. Without it,
a qubit mixture of X and Z refutes the raw noncommutation assertion. -/
theorem noncommutingWeylObstruction (d : ℕ) [NeZero d]
    (a : WeylLabel d → ℝ) (ha : WeylProbabilities a) (hidentity : a (0,0) ≠ 0)
    (l k : WeylLabel d) (hl : a l ≠ 0) (hk : a k ≠ 0)
    (hcomm : finWeyl d l * finWeyl d k ≠ finWeyl d k * finWeyl d l) :
    ¬ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (weylChannel d a) ∧ IsDegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
