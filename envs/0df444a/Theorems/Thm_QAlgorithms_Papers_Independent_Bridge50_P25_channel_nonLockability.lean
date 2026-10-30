-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_channel_nonLockability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.channel_nonLockability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:09:31.040558+00:00
-- url     : https://prove2.me/theorems/46771665-62de-43aa-91a4-53a11839c906
-- title:
--   Corollary V.1: channel non-lockability
-- statement:
--   Let $T^{A\to BC}:M_{d_A}\to M_{d_B}\otimes M_{d_C}$ be a channel in positive finite dimensions, and define $T^{A\to B}=\operatorname{Tr}_C\circ T^{A\to BC}$. Then
--
--   $$E_{\max}(T^{A\to BC})\le2\log_2 d_C+E_{\max}(T^{A\to B}).$$
--
--   The channel quantity optimizes output max-relative entanglement over all normalized inputs and arbitrary finite reference dimensions. There is no restriction relating the input dimension, $d_B$, or $d_C$.
--
--   This transfers state non-lockability to discarding a portion of a channel output.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 17, Corollary V.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Corollary V.1, PDF p.17: reduced channel is tr_C composed with T. -/
theorem channel_nonLockability (T : Superop I (B × C)) (hT : IsChannel T) :
    channelEMax T ≤ (2 * Real.logb 2 (Fintype.card C) : ℝ) +
      channelEMax (reducedChannel T) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
