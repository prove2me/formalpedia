-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_state_nonLockability
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.state_nonLockability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:08:45.240986+00:00
-- url     : https://prove2.me/theorems/3ece3862-9ec4-4252-979d-b4c8a3707943
-- title:
--   Theorem V.1: state non-lockability
-- statement:
--   Let $\rho_{ABB'}$ be any density matrix on positive finite-dimensional systems, and let $\rho_{AB}=\operatorname{Tr}_{B'}\rho_{ABB'}$. The max-relative entanglements across the displayed cuts satisfy
--
--   $$E_{\max}^{A:BB'}(\rho_{ABB'})\le E_{\max}^{A:B}(\rho_{AB})+2\log_2 d_{B'}.$$
--
--   Here $d_{B'}$ is the dimension of the discarded register. Neither purity nor separability is assumed. The addition form is equivalent to the source subtraction because the two state entanglements are finite.
--
--   Thus discarding a subsystem changes this entanglement measure by at most twice its logarithmic dimension.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 16, Theorem V.1

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

/-- Theorem V.1, PDF p.16: equivalent addition form, avoiding extended subtraction. -/
theorem state_nonLockability (rho : Mat (A × (B × C))) (hrho : IsDensityMatrix rho) :
    eMax rho ≤ eMax (forgetExtra rho) + (2 * Real.logb 2 (Fintype.card C) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
