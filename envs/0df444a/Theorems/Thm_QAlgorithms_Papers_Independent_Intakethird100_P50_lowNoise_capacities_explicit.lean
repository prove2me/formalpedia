-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_lowNoise_capacities_explicit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.lowNoise_capacities_explicit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:57:02.43161+00:00
-- url     : https://prove2.me/theorems/6b133881-31ae-4ce2-b86d-c3b4ee7bbf9e
-- title:
--   Theorem 12: explicit joint quantum/private low-noise capacity bounds
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Fix the input/output system $A$. There exist $C_Q,C_P\ge0$ and $0<\delta\le2$, uniform over channels $N:A\to A$ and their dilations, such that $\|N-\mathrm{id}_A\|_\diamond\le\varepsilon$ with $0\le\varepsilon\le\delta$ gives the following. If $\varepsilon=0$ or the actual Choi rank $e$ is one, then $Q(N)=P(N)=I_c(N)$. Otherwise $e\ge2$ and both bounds hold:
--   $$
--   |Q(N)-I_c(N)|\le-3\varepsilon^{3/2}\log_2\varepsilon+2\varepsilon^{3/2}\left[\frac1{\ln2}+\log_2e+\tfrac12\log_2(e-1)\right]+C_Q\varepsilon^{9/2},
--   $$
--   $$
--   |P(N)-I_c(N)|\le-9\varepsilon^{3/2}\log_2\varepsilon+2\varepsilon^{3/2}\left[\frac3{\ln2}+4\log_2e+\log_2(e-1)\right]+C_P\varepsilon^3.
--   $$
--   These are the explicit joint low-noise estimates; the environment's redundant dimension is never substituted for Choi rank.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 12, Theorem 12: explicit joint quantum/private low-noise capacity bounds

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

/-- Theorem 12, PDF p.12: both explicit rank-dependent leading expressions and
remainders, uniform over channels at fixed input dimension. Rank-one and eps=0
are exact branches (the printed log(e-1) expression has no domain there). -/
theorem lowNoise_capacities_explicit [Nonempty A] :
    ∃ Cq Cp : ℝ, 0 ≤ Cq ∧ 0 ≤ Cp ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 2 ∧
      ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E],
      ∀ V : Matrix (A × E) A ℂ, IsIsometry V →
      ∀ eps ∈ Set.Icc 0 delta,
        diamond (channelDifference (receiverChannel V) id) ≤ eps → LowNoiseCapacityBounds V eps Cq Cp := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
