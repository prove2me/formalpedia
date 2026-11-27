-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_21_ville
-- name    : StengelZeroSum.Supplement.theorem_21_ville
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:27:53.947203+00:00
-- url     : https://prove2.me/theorems/b5e37c17-29e8-41f2-a8fb-5fe522a3400f
-- title:
--   Ville's Theorem (21) — $Ax\le0$ has no $x\ge0$, $x\ne0$ iff some $y\ge0$ has $y^\top A>0^\top$
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$). Then
--
--   $$
--   \nexists\,x\in\mathbb R^n:\ Ax\le\mathbf 0,\ x\ge\mathbf 0,\ x\neq\mathbf 0
--   \quad\Longleftrightarrow\quad
--   \exists\,y\in\mathbb R^m:\ y^\top A>\mathbf 0^\top,\ y\ge\mathbf 0 . \tag{21}
--   $$
--
--   Inequalities are componentwise; $y^\top A>\mathbf 0^\top$ means every component of $y^\top A$ is strictly positive. Ville's Theorem is the inequality version of Gordan's Theorem (20) and essentially states the minimax theorem for a game with positive value.
--
--   Differences from the source: none.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Proposition 4, eq. (21), p.9

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- **Ville's Theorem (21)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Proposition 4, eq. (21), p.9
("the Theorem (21) of Ville"): for every `A ∈ ℝ^{m×n}`,
`∄ x ∈ ℝ^n : Ax ≤ 0, x ≥ 0, x ≠ 0  ⇔  ∃ y ∈ ℝ^m : y⊤A > 0⊤, y ≥ 0`.

**Formalization Note** Vector inequalities are componentwise (p.4): `Ax ≤ 0`, `x ≥ 0`,
`y ≥ 0` are `Pi.le`; `x ≠ 0` says some component is nonzero; `y⊤A > 0⊤` is
`∀ j, 0 < (y ᵥ* A) j`. `0 < m`, `0 < n` are the standing assumption (p.4). -/
theorem theorem_21_ville {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    (¬ ∃ x : Fin n → ℝ, A *ᵥ x ≤ 0 ∧ 0 ≤ x ∧ x ≠ 0) ↔
      ∃ y : Fin m → ℝ, (∀ j, 0 < (y ᵥ* A) j) ∧ 0 ≤ y := by sorry

end StengelZeroSum.Supplement
