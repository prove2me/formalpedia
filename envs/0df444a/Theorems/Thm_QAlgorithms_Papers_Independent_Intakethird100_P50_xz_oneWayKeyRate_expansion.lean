-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_xz_oneWayKeyRate_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.xz_oneWayKeyRate_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:04:58.296813+00:00
-- url     : https://prove2.me/theorems/f636563f-b8e0-4fe1-960e-1ca1897cbe3e
-- title:
--   §5 unnumbered cryptographic consequence: optimal XZ one-way key rate
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   For the effective qubit XZ-channel $C_p(\rho)=(1-p)^2\rho+(p-p^2)X\rho X+p^2Y\rho Y+(p-p^2)Z\rho Z$, the source identifies the optimal one-way effective-channel key rate with $P(C_p)$. There exist $K\ge0$ and $0<\delta\le1$ such that
--   $$
--   |P(C_p)-(1-2h(p))|\le Kp^2\log_2(1/p)\qquad(0<p<\delta).
--   $$
--   This is the scalar operational-private-capacity consequence for the stated effective channel, with no quantification over unrelated QKD protocols or two-way attacks. It inherits the numerical-optimizer proof gap disclosed for Corollary 18.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 19, §5 unnumbered cryptographic consequence: optimal XZ one-way key rate

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

/-- §5 cryptographic consequence, PDF p.19: the paper identifies the one-way
EFFECTIVE XZ-channel key rate with its operational private capacity. This scalar
consequence inherits Corollary 18's disclosed numerical-optimizer proof gap. -/
theorem xz_oneWayKeyRate_expansion :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        |fullTracePrivateCapacity (xzDilation p) - (1 - 2 * binEntropy2 p)| ≤
          K * p ^ 2 * (-log2 p) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
