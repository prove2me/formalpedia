-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_pauli_coefficient_constraints
-- name    : SublinearPauli.Fidelity.pauli_coefficient_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:42:08.85356+00:00
-- url     : https://prove2.me/theorems/4ae82da7-9c2b-46cf-a6d7-98a909d69861
-- title:
--   Observation 2 — $\|\hat\rho\|_\infty\le 1/\sqrt d$ and $\|\hat\rho\|_2\le 1$
-- statement:
--   Let $\rho$ be an $N$-qubit density matrix, $d=2^N$, with Pauli coefficients $\hat\rho(Q)=\operatorname{Tr}[\rho Q]/\sqrt d$, $Q\in\mathcal Q$. Then
--   $$\|\hat\rho\|_\infty\le\frac1{\sqrt d},\qquad\|\hat\rho\|_2\le 1.$$
--
--   The first bound is used to trade powers of $|\hat\rho(Q)|$ in Theorem 3 and Lemma 4; the second is the purity bound $\operatorname{Tr}[\rho^2]\le1$.
--
--   Differences from the source:
--   - encoding: $\|\hat\rho\|_\infty=\max_Q|\hat\rho(Q)|$ and $\|\hat\rho\|_2=(\sum_Q\hat\rho(Q)^2)^{1/2}$ → a bound on every $|\hat\rho(Q)|$, and the square root of the sum of squares; reason: equivalent formulations over the finite set $\mathcal Q$.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.8, Observation 2

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Pauli

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- **Observation 2** (Pauli coefficient constraints), p.8. For every `N`-qubit density matrix
`ρ`: `‖ρ̂‖_∞ ≤ 1/√d` and `‖ρ̂‖₂ ≤ 1`, `d = 2^N`. -/
theorem pauli_coefficient_constraints {N : ℕ} (ρ : Op N) (hρ : WildeQIT.IsDensityOperator ρ) :
    (∀ Q : PauliString N, |coeff ρ Q| ≤ 1 / Real.sqrt ((2 : ℝ) ^ N)) ∧
      Real.sqrt (∑ Q : PauliString N, coeff ρ Q ^ 2) ≤ 1 := by sorry

end SublinearPauli.Fidelity
