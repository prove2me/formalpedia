-- Prove2me | Theorems.Thm_VanderbeiLP_StrictComp_farkas_lemma
-- name    : VanderbeiLP.StrictComp.farkas_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T17:42:02.043993+00:00
-- url     : https://prove2.me/theorems/e59835f0-584f-42b7-aa03-f4360b24204b
-- title:
--   Lemma 10.5 — Farkas' Lemma
-- statement:
--   Let $A$ be a real $m \times n$ matrix and $b \in \mathbb{R}^m$. The system of linear inequalities $Ax \le b$, in the unknown $x \in \mathbb{R}^n$ (no sign constraint on $x$), has no solution if and only if there is a $y \in \mathbb{R}^m$ such that
--
--   $$A^T y = 0, \qquad y \ge 0, \qquad b^T y < 0. \qquad (10.8)$$
--
--   Such a $y$ is a certificate of infeasibility: a nonnegative combination of the inequalities whose left-hand side vanishes and whose right-hand side is negative. Farkas' Lemma is the tool behind the Separation Theorem for polyhedra and the strict complementarity results of the same chapter.
--
--   **Formalization Note** Vector inequalities are componentwise. For $m = 0$ the system is always solvable and no $y$ with $b^T y < 0$ exists, consistently with the statement.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 146, Lemma 10.5, Eq. (10.8) (PDF p. 159)

import Mathlib

open Matrix

namespace VanderbeiLP.StrictComp

/-- **Vanderbei, Lemma 10.5 (p. 146), Farkas' Lemma.** The system `Ax ≤ b` (with `x ∈ ℝⁿ`
unrestricted in sign) has no solution iff there is `y ∈ ℝᵐ` with `Aᵀy = 0`, `y ≥ 0`,
`bᵀy < 0` (10.8). -/
theorem farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (¬ ∃ x : Fin n → ℝ, A *ᵥ x ≤ b) ↔
      ∃ y : Fin m → ℝ, Aᵀ *ᵥ y = 0 ∧ 0 ≤ y ∧ b ⬝ᵥ y < 0 := by sorry

end VanderbeiLP.StrictComp
