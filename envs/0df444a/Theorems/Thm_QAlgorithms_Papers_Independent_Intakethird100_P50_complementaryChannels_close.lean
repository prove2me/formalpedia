-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_complementaryChannels_close
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.complementaryChannels_close
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:52:58.954822+00:00
-- url     : https://prove2.me/theorems/88385acc-ef81-4dc8-a04d-f0731e69d401
-- title:
--   Corollary 4: nearby channels admit nearby complementary channels
-- statement:
--   Let $N_1,N_2:\mathcal B(A)\to\mathcal B(B)$ be finite-dimensional quantum channels with $\|N_1-N_2\|_\diamond\le\varepsilon$ and $0\le\varepsilon\le2$. For every isometric dilation $V_1:A\to B\otimes E_1$ of $N_1$, there exist a nonzero finite-dimensional common environment $F$, an isometry $J:E_1\to F$ and an isometric dilation $V_2:A\to B\otimes F$ of $N_2$ such that
--   $$
--   \|J N_1^c(\,\cdot\,)J^\dagger-N_2^c\|_\diamond\le2\sqrt\varepsilon.
--   $$
--   Both complements use the displayed receiver dilations. Enlarging the first environment realizes the paper's equivalence-under-isometry convention without assuming equal minimal Choi ranks.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 6, Corollary 4: nearby channels admit nearby complementary channels

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)

open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- Corollary 4, PDF p.6, with the isometric-equivalence convention of PDF p.4.
FOR ANY first complement, embed its environment into a common larger finite space,
then choose the second complement there. -/
theorem complementaryChannels_close [Nonempty A] [Nonempty B] [Nonempty E]
    (V1 : Matrix (B × E) A ℂ) (hV1 : IsIsometry V1)
    (N2 : Superop A B) (hN2 : IsChannel N2)
    (eps : ℝ) (heps : eps ∈ Set.Icc 0 2)
    (hclose : diamond (channelDifference (receiverChannel V1) N2) ≤ eps) :
    ∃ k : ℕ, 0 < k ∧ ∃ J : Matrix (Fin k) E ℂ, IsIsometry J ∧
      ∃ V2 : Matrix (B × Fin k) A ℂ, IsIsometry V2 ∧ receiverChannel V2 = N2 ∧
        diamond (channelDifference (conjSuperop J ∘ complementaryChannel V1) (complementaryChannel V2)) ≤
          2 * Real.sqrt eps := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
