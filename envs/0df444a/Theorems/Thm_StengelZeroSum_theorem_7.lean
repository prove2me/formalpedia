-- Prove2me | Theorems.Thm_StengelZeroSum_theorem_7
-- name    : StengelZeroSum.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:43.196001+00:00
-- url     : https://prove2.me/theorems/37c910ba-ed29-4c80-b915-c9f093a5e46d
-- title:
--   Theorem 7 — Dantzig's game with one extra row solves the LP pair or certifies infeasibility
-- statement:
--   Let $m,n$ be positive integers, $A$ a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$; consider the primal LP (1) $\max c^\top x$ subject to $Ax\le b$, $x\ge\mathbf0$ and its dual (2) $\min y^\top b$ subject to $y^\top A\ge c^\top$, $y\ge\mathbf0$. For $M\in\mathbb R$ consider the zero-sum game
--
--   $$
--   B_M=\begin{bmatrix}0&A&-b\\-A^\top&0&c\\ b^\top&-c^\top&0\\ \mathbf1^\top&\mathbf1^\top&-M\end{bmatrix}.\qquad(51)
--   $$
--
--   There is some $M_0\in\mathbb R$ such that every $M\ge M_0$ has the following properties:
--
--   1. if (1) and (2) are feasible, they have feasible solutions $x$, $y$ with $\mathbf1^\top x+\mathbf1^\top y+1\le M$;
--   2. $B_M$ has a value, and every value $v$ of $B_M$ satisfies $v\ge0$ and
--      - (a) $v=0$ if and only if (1) and (2) are feasible; in that case, every min-max strategy $(y,x,t)$ of $B_M$ has $(y,x,t,0)$ as a max-min strategy, $t>0$, $x\frac1t$ optimal for (1) and $y\frac1t$ optimal for (2);
--      - (b) if $v>0$, then every max-min strategy $(y,x,r,s)$ has $r=0$, $s=v$ and
--      $$Ax\le\mathbf0,\quad x\ge\mathbf0,\quad A^\top y\ge\mathbf0,\quad y\ge\mathbf0,\quad b^\top y-c^\top x<0,\qquad(52)$$
--      so (1) or (2) is infeasible; moreover $v<1$, and the smallest $w$ such that (53) $A\bar x\le b+\mathbf1w$, $\bar x\ge\mathbf0$, $-A^\top\bar y\le-c+\mathbf1w$, $\bar y\ge\mathbf0$ has feasible solutions is
--      $$w=\frac{M+1}{1/v-1}.\qquad(54)$$
--
--   3. (c) If the entries of $A$, $b$, $c$ are rational numbers, let $\alpha$ be the maximum absolute value of their numerators, $\beta$ their maximum denominator, and $\ell=m+n+1$. Then every
--   $$M\ge \ell!\,\ell\,\alpha^\ell\beta^{\ell^2+\ell}+1\qquad(55)$$
--   has the properties above.
--
--   The theorem reduces solving an LP — finding optimal solutions or a certificate that none exist — to solving one zero-sum game, and in the rational case the reduction is of polynomial size.
--
--   **Formalization Note** The properties are bundled in the predicate of the properties of $M$. In (c), the real data are tied to rational data entrywise, and $\alpha$, $\beta$ come from reduced fractions. The remark after (55) that $M$ has polynomial bit-size concerns encoding length and is not part of the formal claim.
--
--   Differences from the source:
--   - generalization: There is some M ∈ ℝ with the following properties → there is M₀ such that every M ≥ M₀ has the properties; reason: the proof (Theorem 8) works for every M with (59); taking M = M₀ gives the source's claim
--   - generalization: (c) a suitable choice of M is (55) → every M ≥ (55) is suitable; reason: includes M = (55)
--   - reading: (a) v = 0 with min-max strategy (y, x, t) and max-min strategy (y, x, t, 0) … in which case x(1/t) is optimal for (1) and y(1/t) is optimal for (2) → v = 0 iff (1) and (2) are feasible, and when v = 0 every min-max strategy (y, x, t) has (y, x, t, 0) max-min, t > 0, x(1/t) and y(1/t) optimal; reason: the stronger reading of an ambiguous sentence; p.19 argues it for any min-max strategy, and a min-max strategy exists because v is a value
--   - reading: the zero-sum game B_M with value v → B_M has a value, and every v with IsGameValue satisfies the clauses; reason: the paper assumes the minimax theorem (p.13), so the value exists and is unique
--   - reading: α, β the maximum numerator (in absolute value) and denominator of the rational entries → numerators and denominators of the reduced fractions (Rat.num, Rat.den); reason: any other representation only enlarges α, β and hence M, which 'every M ≥ (55)' covers
--   - encoding: k = m + n + 1 columns (y, x, t) and k + 1 rows of B_M → index types (Fin m ⊕ Fin n) ⊕ Unit and ((Fin m ⊕ Fin n) ⊕ Unit) ⊕ Unit; reason: no instance changes
--   - encoding: max-min strategy (y, x, r, s) for B_M → IsMaxMinStrategy … q u for any u; reason: the published predicate carries the max-min value as an argument; no strategy is excluded
--   - encoding: the entries of A, b, c are rational numbers → rational Aq, bq, cq with A i j = Aq i j, b i = bq i, c j = cq j as reals; reason: same instances
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 7, p.18 (and p.19, first line)

import Mathlib
import Definitions.Def_StengelZeroSum_IsSuitableM
import Definitions.Def_StengelZeroSum_bound55

namespace StengelZeroSum

/-- **Theorem 7** (every max-min strategy of Dantzig's game with one extra row solves the LPs or
certifies infeasibility),
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 7,
p.18. For the LP (1) `max c⊤x s.t. Ax ≤ b, x ≥ 0` and its dual (2), there is some `M ∈ ℝ`
with the properties `IsSuitableM` (the feasible-solution bound `1⊤x + 1⊤y + 1 ≤ M`, `v ≥ 0`,
parts (a) and (b) for the game `B_M` of (51)); and (c) if the entries of `A, b, c` are
rational, `M = ℓ! ℓ α^ℓ β^(ℓ²+ℓ) + 1` (55) is a suitable choice.

**Formalization Note** "There is some M" is stated as: every `M ≥ M₀` is suitable, for some
`M₀`; and (c) as: every `M ≥ (55)` is suitable. Both specialise to the paper's statements
(`M = M₀`, `M = (55)`). In (c) the real data are tied to rational data by
`A i j = Aq i j`, `b i = bq i`, `c j = cq j`, with `α`, `β` taken from the reduced fractions.
The remark after (55) that `M` has polynomial bit-size is a comment on encoding length, not
part of the claim. `m, n > 0` is the paper's standing assumption (p.4). -/
theorem theorem_7 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    (∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → IsSuitableM A b c M) ∧
    ∀ (Aq : Matrix (Fin m) (Fin n) ℚ) (bq : Fin m → ℚ) (cq : Fin n → ℚ),
      (∀ i j, A i j = (Aq i j : ℝ)) → (∀ i, b i = (bq i : ℝ)) → (∀ j, c j = (cq j : ℝ)) →
      ∀ M : ℝ, bound55 Aq bq cq ≤ M → IsSuitableM A b c M := by sorry

end StengelZeroSum
