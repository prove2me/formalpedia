-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_2
-- name    : StengelZeroSum.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:27:18.303725+00:00
-- url     : https://prove2.me/theorems/01026728-c2b8-4cd6-b1cc-0acebb9cf17a
-- title:
--   Theorem 2 (The minimax theorem) — optimal values of (7) and (8) coincide, $u=v$
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$), the payoff matrix of a zero-sum game with a maximizing row player and a minimizing column player. Let $Y=\{y\in\mathbb R^m\mid y\ge\mathbf 0,\ \mathbf 1^\top y=1\}$ and $X=\{x\in\mathbb R^n\mid x\ge\mathbf 0,\ \mathbf 1^\top x=1\}$ be the sets of mixed strategies (4), (5). Consider the LPs
--
--   $$
--   \text{(7)}\ \ \min_{x,v}\ v\ \ \text{s.t.}\ Ax\le\mathbf 1v,\ x\in X,
--   \qquad
--   \text{(8)}\ \ \max_{y,u}\ u\ \ \text{s.t.}\ y^\top A\ge u\mathbf 1^\top,\ y\in Y .
--   $$
--
--   An optimal solution $(x,v)$ of (7) is a **min-max strategy** $x$ with min-max value $v$, and an optimal solution $(y,u)$ of (8) is a **max-min strategy** $y$ with max-min value $u$. Then:
--
--   1. (7) has an optimal solution and (8) has an optimal solution;
--   2. for every optimal $(x,v)$ of (7) and every optimal $(y,u)$ of (8),
--
--   $$
--   u=v ,
--   $$
--
--   the value of the game.
--
--   This is von Neumann's minimax theorem stated through the two LPs (7) and (8).
--
--   **Formalization Note** "Optimal for (7)" and "optimal for (8)" are the published `IsMinMaxStrategy A x v` and `IsMaxMinStrategy A y u` of `ZeroSumLP.DantzigExt`; that $x$ is then a min-max strategy and $y$ a max-min strategy holds by these definitions.
--
--   Differences from the source:
--   - generalization: the theorem considers given optimal solutions of (7) and (8) → Lean also asserts that optimal solutions of (7) and (8) exist; reason: the paper notes (p.9) that the min-max and max-min values exist without LP duality, and the stated existence makes the equality non-vacuous; the third conjunct is exactly the source's claim.
--   - encoding: "x is a min-max strategy, and y is a max-min strategy" → not a separate conjunct; reason: in the paper's definitions (p.6) an optimal solution of (7) (resp. (8)) is a min-max (resp. max-min) strategy, so these clauses hold by definition of `IsMinMaxStrategy`/`IsMaxMinStrategy`.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 2, p.6 (LPs (7), (8), p.6; strategy sets (4), (5), p.5)

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame

open Matrix ZeroSumLP.DantzigExt

namespace StengelZeroSum.Supplement

/-- **Theorem 2 (The minimax theorem)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 2, p.6:
"Consider optimal `x, v` for (7) and `y, u` for (8). Then `u = v` (the value of the game),
`x` is a min-max strategy, and `y` is a max-min strategy."

(7) is `minimize v subject to Ax ≤ 1v, x ∈ X`, (8) is `maximize u subject to y⊤A ≥ u1⊤,
y ∈ Y`, with `X`, `Y` the mixed-strategy simplices (4), (5).

**Formalization Note** "Optimal `x, v` for (7)" is the published `IsMinMaxStrategy A x v` and
"optimal `y, u` for (8)" is `IsMaxMinStrategy A y u` (`ZeroSumLP.DantzigExt`), which are by
definition a min-max and a max-min strategy; the content is `u = v`. The statement also asserts
that optimal solutions of (7) and (8) exist (the paper notes on p.9 that they exist without LP
duality), so the equality is not vacuous. `0 < m`, `0 < n` are the standing assumption (p.4). -/
theorem theorem_2 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∃ (x : Fin n → ℝ) (v : ℝ), IsMinMaxStrategy A x v) ∧
      (∃ (y : Fin m → ℝ) (u : ℝ), IsMaxMinStrategy A y u) ∧
      ∀ (x : Fin n → ℝ) (v : ℝ) (y : Fin m → ℝ) (u : ℝ),
        IsMinMaxStrategy A x v → IsMaxMinStrategy A y u → u = v := by sorry

end StengelZeroSum.Supplement
