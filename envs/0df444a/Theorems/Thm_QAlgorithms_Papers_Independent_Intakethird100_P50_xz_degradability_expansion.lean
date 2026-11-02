-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_xz_degradability_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.xz_degradability_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:02:36.206203+00:00
-- url     : https://prove2.me/theorems/32de291d-aed5-48f0-bc26-5fb137262be4
-- title:
--   Theorem 17: sharper equal-error XZ degradability expansion
-- statement:
--   Let $C_p$ be the qubit channel with independent X and Z errors, each of probability $p$:
--   $$
--   C_p(\rho)=(1-p)^2\rho+(p-p^2)X\rho X+p^2Y\rho Y+(p-p^2)Z\rho Z.
--   $$
--   Use the canonical four-label dilation. There exist $K\ge0$ and $0<\delta\le1$ such that
--   $$
--   \operatorname{dg}(C_p)\le16p^2+32p^{5/2}+Kp^3\qquad(0<p<\delta).
--   $$
--   The degradability parameter minimizes full diamond error over CPTP degrading maps. The fractional-power term is part of the sharper asserted expansion.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 17, Theorem 17: sharper equal-error XZ degradability expansion

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

/-- Theorem 17, PDF p.17: retains the fractional-power 32 p^(5/2) term.
The canonical XZ dilation has independent equal X and Z error probabilities p. -/
theorem xz_degradability_expansion :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ Set.Ioo 0 delta,
        degradability (xzDilation p) ≤
          16 * p ^ 2 + 32 * p ^ (5 / 2 : ℝ) + K * p ^ 3 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
