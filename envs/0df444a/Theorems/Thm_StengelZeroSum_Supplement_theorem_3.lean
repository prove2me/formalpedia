-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_3
-- name    : StengelZeroSum.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:28:27.090883+00:00
-- url     : https://prove2.me/theorems/3abb8469-8579-4eae-81ef-e87177ade66b
-- title:
--   Theorem 3 (Stiemke) — no $y$ has $y^\top A\ge0^\top$, $y^\top A\ne0$ iff $Ax=0$ for some $x>0$
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$). Then
--
--   $$
--   \nexists\,y\in\mathbb R^m:\ y^\top A\ge\mathbf 0^\top,\ y^\top A\neq\mathbf 0
--   \quad\Longleftrightarrow\quad
--   \exists\,x\in\mathbb R^n:\ Ax=\mathbf 0,\ x>\mathbf 0 . \tag{23}
--   $$
--
--   Inequalities are componentwise: $y^\top A\neq\mathbf 0$ means some component of $y^\top A$ is nonzero, and $x>\mathbf 0$ means every component of $x$ is strictly positive. In words: $\mathbf 0^\top$ is the only nonnegative vector in the row space of $A$ exactly when the null space of $A$ contains a strictly positive vector. The paper uses Stiemke's Theorem to prove Gordan's Theorem (20) (Proposition 5).
--
--   Differences from the source: none.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 3, eq. (23), p.10

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- **Theorem 3 (Stiemke)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 3, eq. (23), p.10: for `A ∈ ℝ^{m×n}`,
`∄ y ∈ ℝ^m : y⊤A ≥ 0⊤, y⊤A ≠ 0  ⇔  ∃ x ∈ ℝ^n : Ax = 0, x > 0`.

**Formalization Note** Vector inequalities are componentwise (p.4): `y⊤A ≥ 0⊤` is
`0 ≤ y ᵥ* A`, `y⊤A ≠ 0` says some component is nonzero, and `x > 0` says every component
is strictly positive, `∀ j, 0 < x j` (not Lean's `Pi.lt`). `0 < m`, `0 < n` are the
standing assumption (p.4). -/
theorem theorem_3 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    (¬ ∃ y : Fin m → ℝ, 0 ≤ y ᵥ* A ∧ y ᵥ* A ≠ 0) ↔
      ∃ x : Fin n → ℝ, A *ᵥ x = 0 ∧ ∀ j, 0 < x j := by sorry

end StengelZeroSum.Supplement
