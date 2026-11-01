-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_fawziRenner
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.fawziRenner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:51:38.219142+00:00
-- url     : https://prove2.me/theorems/525cdb69-6ee0-4372-8565-f0ebb88e130e
-- title:
--   Fawzi–Renner lower bound in bits
-- statement:
--   Let $\rho_{ABC}$ be any density operator on finite-dimensional nonzero complex systems. Let $F(A;B|C)_\rho$ be the maximum squared fidelity with states recovered from $\rho_{BC}$ by an arbitrary CPTP map $C\to AC$, acting identically on $B$. Then
--
--   $$
--   I(A:B|C)_\rho\ge-\log_2 F(A;B|C)_\rho.
--   $$
--
--   The conditional mutual information is $H(AC)+H(BC)-H(ABC)-H(C)$ with entropy in bits. The negative logarithm at zero is interpreted as $+\infty$. This is Theorem 5, reproved operationally in this paper, with no full-rank or Markov-state restriction.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 6, Theorem 5, (37),(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P75

namespace QAlgorithms.Papers.Independent.Intakenext100.P75

open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

variable {A B C D Ap Bp Cp R I J K L : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype Ap] [DecidableEq Ap] [Nonempty Ap]

variable [Fintype Bp] [DecidableEq Bp] [Nonempty Bp]

variable [Fintype Cp] [DecidableEq Cp] [Nonempty Cp]

variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- Theorem 5, PDF p.6, (37), proved through p.7, (47): Fawzi–Renner
in bits. Extended negative log at zero is +infinity. -/
theorem fawziRenner
    [Nonempty A] [Nonempty B] [Nonempty C] (rho : Mat (B × (A × C))) (hrho : IsDensityMatrix rho) :
    (if ordinaryRecovery rho = 0 then (⊤ : EReal)
      else ((-Real.logb 2 (ordinaryRecovery rho) : ℝ) : EReal)) ≤ (conditionedLastCMIBits rho : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
