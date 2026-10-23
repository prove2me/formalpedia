-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_weylMultiplierObstruction
-- name    : QAlgorithms.Papers.Independent.Gap20.P19.weylMultiplierObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:36:28.536054+00:00
-- url     : https://prove2.me/theorems/374ac38d-b6d4-415b-868d-b30479619dbb
-- title:
--   Theorem 13
-- statement:
--   All Hilbert spaces are finite dimensional, complex, and nonzero. A channel is completely positive and trace preserving on every operator. Write $r(\Phi)$ for its Choi rank, the minimum pure-environment dimension. Receiver and complementary channels are always obtained from the same isometry.
--
--   For an integer $d\ge1$, let $V_{j,k}=X^jZ^k$ with labels in $\mathbb Z_d^2$, forward cyclic shift $X$ and positive-phase clock $Z$. Let $a_m\ge0$, $\sum_m a_m=1$, and $P_a(\rho)=\sum_m a_mV_m\rho V_m^\dagger$. These $a_m$ are probabilities.
--
--   Assume $a_{0,0}\ne0$. Define $\varphi_m=d^{-1}\operatorname{Tr}[V_m^\dagger P_a(V_m)]$. If some nonidentity supported label $m$ has $0<|\varphi_m|<1$, then
--   $$P_a\text{ is not degradable}.$$
--
--   The computed normalized coefficient supplies a concrete obstruction, without a prime-dimension restriction.
-- source:
--   The structure of degradable quantum channels, arXiv:0802.1360v2, PDF p. 21, Theorem 13

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

/-- Theorem 13, PDF p.21: arbitrary positive d, with identity in the support.
The multiplier is computed with the missing 1/d normalization restored. -/
theorem weylMultiplierObstruction (d : ℕ) [NeZero d]
    (a : WeylLabel d → ℝ) (ha : WeylProbabilities a) (hidentity : a (0,0) ≠ 0)
    (m : WeylLabel d) (hm : m ≠ (0,0)) (ham : a m ≠ 0)
    (hlo : 0 < ‖weylMultiplier d a m‖) (hhi : ‖weylMultiplier d a m‖ < 1) :
    ¬ (∃ envSize : ℕ, ∃ witness : Matrix (_ × Fin envSize) _ ℂ, receiverChannel witness = (weylChannel d a) ∧ IsDegradable witness) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P19

end
