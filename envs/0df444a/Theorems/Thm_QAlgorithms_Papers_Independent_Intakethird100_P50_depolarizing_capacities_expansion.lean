-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_depolarizing_capacities_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.depolarizing_capacities_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:59:55.945131+00:00
-- url     : https://prove2.me/theorems/18bd95d7-8b7b-4652-be5c-b608fd747e1e
-- title:
--   Theorem 14: depolarizing quantum and private capacities through the leading quadratic-log correction
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces. A channel is complex-linear, completely positive and trace preserving. Its receiver and full complementary channel are obtained from the same isometric dilation. Write $Q(N)$ and $P(N)$ for the unassisted operational quantum and private capacities, allowing arbitrary collective codes over independent uses with vanishing reliability error and environmental leakage. Write $I_c(N)=\max_\rho[S(N(\rho))-S(N^c(\rho))]$, where the maximum includes every density operator. Entropies and logarithms are in bits, with $0\log 0=0$. The diamond norm has no factor $1/2$.
--
--   Let $D_p(\rho)=(1-p)\rho+\frac p3(X\rho X+Y\rho Y+Z\rho Z)$ and set $b(p)=1-h(p)-p\log_2 3$, where $h$ is binary entropy in bits. There exist $K_Q,K_P\ge0$ and $0<\delta\le1$ such that for every $0<p<\delta$,
--   $$
--   b(p)\le Q(D_p)\le b(p)-\frac{16}{9}(6+\sqrt2)p^2\log_2p+K_Qp^2,
--   $$
--   $$
--   b(p)\le P(D_p)\le b(p)-\frac{16}{3}(6+\sqrt2)p^2\log_2p+K_Pp^2.
--   $$
--   Both lower and upper bounds are retained. The displayed hashing expression is used only in the low-noise regime.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 15, Theorem 14: depolarizing quantum and private capacities through the leading quadratic-log correction

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

/-- Theorem 14, PDF p.15: both lower and upper bounds for both operational
capacities, with the factor-three private/quantum leading correction. -/
theorem depolarizing_capacities_expansion :
    ∃ Kq Kp : ℝ, 0 ≤ Kq ∧ 0 ≤ Kp ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        (depolarizingHashing p ≤ dilationQuantumCapacity (depolarizingDilation p) ∧
          dilationQuantumCapacity (depolarizingDilation p) ≤ depolarizingHashing p -
            (16 / 9 : ℝ) * (6 + Real.sqrt 2) * p ^ 2 * log2 p + Kq * p ^ 2) ∧
        (depolarizingHashing p ≤ fullTracePrivateCapacity (depolarizingDilation p) ∧
          fullTracePrivateCapacity (depolarizingDilation p) ≤ depolarizingHashing p -
            (16 / 3 : ℝ) * (6 + Real.sqrt 2) * p ^ 2 * log2 p + Kp * p ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
