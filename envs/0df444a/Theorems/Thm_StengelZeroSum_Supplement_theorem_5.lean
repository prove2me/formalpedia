-- Prove2me | Theorems.Thm_StengelZeroSum_Supplement_theorem_5
-- name    : StengelZeroSum.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:29:04.327475+00:00
-- url     : https://prove2.me/theorems/3b2b5b16-f4c3-5c0c-b966-05a043754321
-- title:
--   Theorem 5 (Dantzig) — Dantzig's game $B$ has value $0$; a min-max strategy with $t>0$ solves the LPs, $(Bz)_k<0$ certifies infeasibility
-- statement:
--   Let $A$ be a real $m\times n$ matrix ($m,n\ge1$), $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $B$ be Dantzig's game (35), with $k=m+n+1$ rows and columns indexed by $(y,x,t)$:
--
--   $$
--   B=\begin{bmatrix} 0 & A & -b\\ -A^\top & 0 & c\\ b^\top & -c^\top & 0\end{bmatrix}.
--   $$
--
--   Write a strategy as $z=(y,x,t)\in\mathbb R^m\times\mathbb R^n\times\mathbb R$, so $z_k=t$. Then:
--
--   1. $B$ has value zero: a real $v$ is a min-max value of $B$ if and only if $v=0$.
--   2. There is a min-max strategy $z$ of $B$ (with min-max value $0$) that is also a max-min strategy (with max-min value $0$), with $Bz\le\mathbf 0$.
--   3. For every min-max strategy $z=(y,x,t)$ of $B$: if $z_k=t>0$, then $x\frac1t$ is an optimal solution of the primal LP (1) and $y\frac1t$ is an optimal solution of the dual LP (2).
--   4. For every min-max strategy $z=(y,x,t)$ of $B$: if $(Bz)_k<0$, then $t=0$ and at least one of the LPs (1) or (2) is infeasible.
--
--   Here (1) is $\max c^\top x$ s.t. $Ax\le b$, $x\ge\mathbf 0$, and (2) is $\min y^\top b$ s.t. $y^\top A\ge c^\top$, $y\ge\mathbf 0$. Theorem 5 is Dantzig's classic derivation of LP duality from the minimax theorem; its known gap is a min-max strategy with $z_k=0$ and $(Bz)_k=0$, which the extra row of Theorem 7 removes.
--
--   **Formalization Note** $B$ is `dantzigGame A b c`, indexed by $(\mathrm{Fin}\,m\oplus\mathrm{Fin}\,n)\oplus\mathrm{Unit}$ with the last index the $k$th coordinate $t$. Min-max and max-min strategies and the value are the published `IsMinMaxStrategy`, `IsMaxMinStrategy`, `IsGameValue` of (7), (8); the LPs (1), (2) are the published `VanderbeiLP.StrictComp` definitions.
--
--   Differences from the source:
--   - generalization: the two "If" clauses speak of the min-max strategy $z$ exhibited in the preceding sentence → Lean asserts them for every min-max strategy $z$ of $B$ (with any min-max value $v$); reason: the paper's proof uses only $z\in X$ and $Bz\le\mathbf 0$, which hold for every min-max strategy once the value is $0$; the exhibited $z$ is one such strategy, so this specializes to the source.
--   - encoding: "B has value zero" → `∀ v, IsGameValue B v ↔ v = 0`; reason: the value is the optimal value of (7), which exists; same meaning.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 5, eq. (35), p.13 (proof pp.13–14)

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair
import Definitions.Def_StengelZeroSum_Supplement_dantzigGame

open Matrix ZeroSumLP.DantzigExt VanderbeiLP.StrictComp

namespace StengelZeroSum.Supplement

/-- **Theorem 5 (Dantzig)**, von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 5, p.13:
"Let `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, `c ∈ ℝ^n`. Consider the zero-sum game with the payoff matrix
`B` (with `k = m + n + 1` rows and columns) defined by (35). Then `B` has value zero, with a
min-max strategy `z = (y, x, t) ∈ ℝ^m × ℝ^n × ℝ` that is also a max-min strategy, with
`Bz ≤ 0`. If `z_k = t > 0` then `x(1/t)` is an optimal solution to the primal LP (1) and
`y(1/t)` is an optimal solution to dual LP (2). If `(Bz)_k < 0` then `t = 0` and at least one
of the LPs (1) or (2) is infeasible."

Stated as four conjuncts: (1) the reals `v` that are a value of `B` are exactly `0`;
(2) some `z` is a min-max strategy of `B` with min-max value `0`, a max-min strategy with
max-min value `0`, and `Bz ≤ 0`; (3) and (4) the two "If" clauses, for **every** min-max
strategy `z` of `B`.

**Formalization Note** `B` is `dantzigGame A b c`, indexed `(Fin m ⊕ Fin n) ⊕ Unit` in the
order `(y, x, t)`: `y_i = z (.inl (.inl i))`, `x_j = z (.inl (.inr j))`, `t = z_k = z (.inr ())`,
and `(Bz)_k = (B *ᵥ z) (.inr ())`. "Value" and "min-max/max-min strategy" are the published
`IsGameValue`, `IsMinMaxStrategy`, `IsMaxMinStrategy` of (7), (8). The paper's clauses speak of
the `z` just exhibited; here they are asserted for every min-max strategy `z` (with its min-max
value `v`), which contains the paper's case. (1), (2) are the LPs of `VanderbeiLP.StrictComp`.
`0 < m`, `0 < n` are the standing assumption (p.4). -/
theorem theorem_5 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    (∀ v : ℝ, IsGameValue (dantzigGame A b c) v ↔ v = 0) ∧
    (∃ z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ,
      IsMinMaxStrategy (dantzigGame A b c) z 0 ∧ IsMaxMinStrategy (dantzigGame A b c) z 0 ∧
        dantzigGame A b c *ᵥ z ≤ 0) ∧
    (∀ (z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ) (v : ℝ), IsMinMaxStrategy (dantzigGame A b c) z v →
      0 < z (.inr ()) →
        PrimalOptimal A b c (fun j => z (.inl (.inr j)) / z (.inr ())) ∧
          DualOptimal A b c (fun i => z (.inl (.inl i)) / z (.inr ()))) ∧
    (∀ (z : (Fin m ⊕ Fin n) ⊕ Unit → ℝ) (v : ℝ), IsMinMaxStrategy (dantzigGame A b c) z v →
      (dantzigGame A b c *ᵥ z) (.inr ()) < 0 →
        z (.inr ()) = 0 ∧
          ((¬ ∃ x : Fin n → ℝ, PrimalFeasible A b x) ∨
            (¬ ∃ y : Fin m → ℝ, DualFeasible A c y))) := by sorry

end StengelZeroSum.Supplement
