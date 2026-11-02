-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_depolarizing_degradability_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.depolarizing_degradability_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:59:05.143453+00:00
-- url     : https://prove2.me/theorems/1c1385c2-0a11-479d-af90-9428989c9b58
-- title:
--   Theorem 13: improved depolarizing degradability coefficient
-- statement:
--   For $0\le p\le1$, define the qubit depolarizing channel $D_p(\rho)=(1-p)\rho+\frac p3(X\rho X+Y\rho Y+Z\rho Z)$, using the canonical dilation with Kraus labels $I,X,Y,Z$. Thus $p$ is the total Pauli error. There exist $K\ge0$ and $0<\delta\le1$ such that
--   $$
--   \operatorname{dg}(D_p)\le\frac89(6+\sqrt2)p^2+Kp^3\qquad(0<p<\delta).
--   $$
--   Here $\operatorname{dg}$ minimizes full diamond error over all CPTP degrading maps. This retains the improved depolarizing coefficient rather than the rough preliminary bound.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 13, Theorem 13: improved depolarizing degradability coefficient

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

/-- Theorem 13, PDF pp.13–15: improved 8/9(6+sqrt 2) coefficient and cubic
remainder; p is total Pauli error. -/
theorem depolarizing_degradability_expansion :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        degradability (depolarizingDilation p) ≤
          (8 / 9 : ℝ) * (6 + Real.sqrt 2) * p ^ 2 + K * p ^ 3 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
