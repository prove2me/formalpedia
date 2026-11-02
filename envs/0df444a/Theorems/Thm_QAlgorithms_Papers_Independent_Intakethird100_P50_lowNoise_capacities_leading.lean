-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_lowNoise_capacities_leading
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.lowNoise_capacities_leading
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:50:22.397518+00:00
-- url     : https://prove2.me/theorems/42f307ee-3cc2-4ad6-8743-082f0519a198
-- title:
--   Abstract main result: both low-noise capacities agree with one-shot coherent information to leading orders
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Fix the input/output space $A$. There are constants $C\ge0$ and $0<\delta\le1$, uniform over all channels $N:A\to A$ and their dilations, such that $\|N-\mathrm{id}_A\|_\diamond\le\varepsilon$ and $0<\varepsilon<\delta$ imply
--   $$
--   \max\{|Q(N)-I_c(N)|,\ |P(N)-I_c(N)|\}\le C\varepsilon^{3/2}\log_2(1/\varepsilon).
--   $$
--   This quantifies the joint leading-order agreement asserted in the abstract using Theorem 12.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 1, Abstract main result: both low-noise capacities agree with one-shot coherent information to leading orders

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

/-- Abstract, PDF p.1, pinned to Theorem 12, PDF p.12: both operational capacities
agree with unrestricted one-shot coherent information up to O(eps^(3/2) log(1/eps)).
Constants are uniform over channels and dilations for each fixed input dimension. -/
theorem lowNoise_capacities_leading [Nonempty A] :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E],
      ∀ V : Matrix (A × E) A ℂ, IsIsometry V →
      ∀ eps ∈ Set.Ioo 0 delta,
        diamond (channelDifference (receiverChannel V) id) ≤ eps →
        |dilationQuantumCapacity V - maximumCoherentInformation V| ≤
          C * eps ^ (3 / 2 : ℝ) * (-log2 eps) ∧
        |fullTracePrivateCapacity V - maximumCoherentInformation V| ≤
          C * eps ^ (3 / 2 : ℝ) * (-log2 eps) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
