-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_4
-- name    : StengelZeroSum.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:28:40.30956+00:00
-- url     : https://prove2.me/theorems/db8551ba-c631-575b-853d-84dd6d37f04d
-- title:
--   Theorem 4 (Loomis) — for $B>0$ some $x\in X$, $y\in Y$, $v$ have $Ax\le Bxv$ and $y^\top A\ge vy^\top B$
-- statement:
--   Let $A$ and $B$ be two real $m\times n$ matrices ($m,n\ge1$) with $B>0$, that is, every entry of $B$ is strictly positive. Let $Y=\{y\in\mathbb R^m\mid y\ge\mathbf 0,\ \mathbf 1^\top y=1\}$ and $X=\{x\in\mathbb R^n\mid x\ge\mathbf 0,\ \mathbf 1^\top x=1\}$. Then there exist $x\in X$, $y\in Y$ and $v\in\mathbb R$ such that
--
--   $$
--   Ax\le Bx\,v
--   \qquad\text{and}\qquad
--   y^\top A\ge v\,y^\top B ,
--   $$
--
--   componentwise: $(Ax)_i\le v\,(Bx)_i$ for every row $i$ and $(y^\top A)_j\ge v\,(y^\top B)_j$ for every column $j$.
--
--   The case $B=\mathbf 1\mathbf 1^\top$ is the minimax theorem.
--
--   Differences from the source: none.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 4, p.12 (X and Y from (4), (5), p.5)

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- **Theorem 4 (Loomis)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 4, p.12:
"Let `A` and `B` be two `m × n` matrices with `B > 0`. Then there exist `x ∈ X`, `y ∈ Y`,
and `v ∈ ℝ` such that `Ax ≤ Bxv` and `y⊤A ≥ vy⊤B`."
Here `Y = {y ∈ ℝ^m | y ≥ 0, 1⊤y = 1}` (4) and `X = {x ∈ ℝ^n | x ≥ 0, 1⊤x = 1}` (5).

**Formalization Note** `B > 0` is entrywise strict positivity, `∀ i j, 0 < B i j` (p.4).
`Ax ≤ Bxv` is `(Ax)_i ≤ (Bx)_i · v` for every row `i`, and `y⊤A ≥ vy⊤B` is
`v · (y⊤B)_j ≤ (y⊤A)_j` for every column `j`. `0 < m`, `0 < n` are the standing
assumption (p.4). -/
theorem theorem_4 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A B : Matrix (Fin m) (Fin n) ℝ)
    (hB : ∀ i j, 0 < B i j) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ) (v : ℝ),
      (0 ≤ x ∧ ∑ j, x j = 1) ∧ (0 ≤ y ∧ ∑ i, y i = 1) ∧
      (∀ i, (A *ᵥ x) i ≤ (B *ᵥ x) i * v) ∧ (∀ j, v * (y ᵥ* B) j ≤ (y ᵥ* A) j) := by sorry

end StengelZeroSum.Supplement
