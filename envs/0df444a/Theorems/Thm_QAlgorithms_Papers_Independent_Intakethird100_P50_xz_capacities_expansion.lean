-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_xz_capacities_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.xz_capacities_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:03:21.654722+00:00
-- url     : https://prove2.me/theorems/dff32790-17cd-4cac-a763-84aba96a493f
-- title:
--   Corollary 18: explicit XZ quantum/private capacity expansion
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Let $C_p(\rho)=(1-p)^2\rho+(p-p^2)X\rho X+p^2Y\rho Y+(p-p^2)Z\rho Z$, representing independent equal X and Z error probabilities $p$. There exist $K_Q,K_P\ge0$ and $0<\delta\le1$ such that for every $0<p<\delta$,
--   $$
--   1-2h(p)\le Q(C_p)\le1-2h(p)-32p^2\log_2p+K_Qp^2,
--   $$
--   $$
--   1-2h(p)\le P(C_p)\le1-2h(p)-96p^2\log_2p+K_Pp^2.
--   $$
--   This is the unconditional numbered corollary, with both capacities and both sides of each bound.
--
--   **Source Note.** The preceding source text supports its optimizing-input identity only by numerics. The corollary is transcribed with that proof gap disclosed, without adding an optimizer hypothesis.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 18, Corollary 18: explicit XZ quantum/private capacity expansion

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

/-- Corollary 18, PDF p.18: unconditional printed statement, including both upper
and lower bounds. The preceding optimizer identity is supported only by numerics
in the source; this proof gap is disclosed, not converted to an extra hypothesis. -/
theorem xz_capacities_expansion :
    ∃ Kq Kp : ℝ, 0 ≤ Kq ∧ 0 ≤ Kp ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        (1 - 2 * binEntropy2 p ≤ dilationQuantumCapacity (xzDilation p) ∧
          dilationQuantumCapacity (xzDilation p) ≤
            1 - 2 * binEntropy2 p - 32 * p ^ 2 * log2 p + Kq * p ^ 2) ∧
        (1 - 2 * binEntropy2 p ≤ fullTracePrivateCapacity (xzDilation p) ∧
          fullTracePrivateCapacity (xzDilation p) ≤
            1 - 2 * binEntropy2 p - 96 * p ^ 2 * log2 p + Kp * p ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
