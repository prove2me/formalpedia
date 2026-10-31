-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P03_cyclotomic_values_at_signs
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P03.cyclotomic_values_at_signs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:54:09.588267+00:00
-- url     : https://prove2.me/theorems/c75895d6-ce7d-44da-ae6c-c578bd256e75
-- title:
--   Values of integer cyclotomic polynomials at both signs
-- statement:
--   Let $\Phi_d\in\mathbb Z[X]$ be the monic $d$th cyclotomic polynomial. Then
--
--   $$\begin{aligned}
--   d\ge3,\ d\notin\{2^j:j\in\mathbb N\}&\Longrightarrow\Phi_d(1),\Phi_d(-1)\text{ are odd},\\
--   k\ge2&\Longrightarrow\Phi_{2^k}(1)=\Phi_{2^k}(-1)=2.
--   \end{aligned}$$
--
--   This result is independent of the gate parameter $n$. It provides the parity input for the normalized-numerator argument.
-- source:
--   Exact synthesis of single-qubit unitaries over Clifford-cyclotomic gate sets, arXiv:1501.04944v2, PDF p. 15, Theorem 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P03

open scoped BigOperators Classical

-- Reuse the Mathlib matrix type without declaring a second Mat.

local notation "Mat" => Matrix Bool Bool ℂ

/-- Canonical data: the axis/exponent list and the actual residual matrix D,
not a nonunique phase/Clifford witness pair, PDF pp.6-7. -/
local notation "CanonicalData" => List (Fin 3 × ℕ) × Matrix Bool Bool ℂ

/-- Theorem 6.2, PDF pp.15-16. The cyclotomic variable is independent of
the gate parameter; both signs and both regimes appear in this one statement. -/
theorem cyclotomic_values_at_signs :
    (∀ d : ℕ, 3 ≤ d → ¬ IsTwoPower d →
      Odd ((Polynomial.cyclotomic d ℤ).eval 1) ∧
      Odd ((Polynomial.cyclotomic d ℤ).eval (-1))) ∧
    (∀ k : ℕ, 2 ≤ k →
      (Polynomial.cyclotomic (2 ^ k) ℤ).eval 1 = 2 ∧
      (Polynomial.cyclotomic (2 ^ k) ℤ).eval (-1) = 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P03

end
