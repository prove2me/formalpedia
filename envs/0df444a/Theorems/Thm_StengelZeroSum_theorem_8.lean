-- Prove2me | Theorems.Thm_StengelZeroSum_theorem_8
-- name    : StengelZeroSum.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:52.422552+00:00
-- url     : https://prove2.me/theorems/780ac1cb-4c1d-4dd8-ba1a-7617de93530e
-- title:
--   Theorem 8 — the game $D_M$ either has value $0$ or certifies infeasibility of $Cz\le d$
-- statement:
--   Let $C$ be a real $k\times k$ matrix with $C=-C^\top$ and let $d\in\mathbb R^k$. Let $(z^*,w^*)$ minimize $w$ subject to
--
--   $$
--   Cz-\mathbf1w\le d,\qquad d^\top z-w\le0,\qquad z\ge\mathbf0,\qquad w\ge0,\qquad(58)
--   $$
--
--   and let $M\in\mathbb R$ with $\mathbf1^\top z^*+1\le M$ (59). Consider the zero-sum game
--
--   $$
--   D_M=\begin{bmatrix}C&-d\\ d^\top&0\\ \mathbf1^\top&-M\end{bmatrix}.\qquad(60)
--   $$
--
--   Then $D_M$ has a value, and every value $v$ of $D_M$ satisfies $v\ge0$ and
--
--   1. (a) $v=0$ if and only if $w^*=0$. If $w^*=0$, let $t=\frac1{\mathbf1^\top z^*+1}$ and $z=z^*t$; then $(z,t)$ is a min-max strategy and $(z,t,0)$ is a max-min strategy of $D_M$, both with value $0$.
--   2. (b) If $v>0$, then every max-min strategy $(q,r,s)$ of $D_M$ satisfies $r=0$, $s=v$ and
--   $$Cq\le\mathbf0,\qquad d^\top q<0,\qquad(61)$$
--   and there is no $z\ge\mathbf0$ with $Cz\le d$.
--
--   Applied to $C$, $d$ of (57), this is the core of Theorem 7: it turns the LP pair (1)/(2) into the game $B_M$.
--
--   **Formalization Note** The $k$ coordinates form a nonempty finite type. Column strategies are $(z,t)$, row strategies $(q,r,s)$.
--
--   Differences from the source:
--   - generalization: (z*, w*) a basic feasible solution that minimizes w subject to (58) → (z*, w*) any minimizer of w subject to (58); reason: the proof of Theorem 8 uses only (58), minimality and (59), never basicness; basic minimizers are a special case
--   - reading: consider the zero-sum game D_M with game value v → D_M has a value, and every v with IsGameValue satisfies the conclusions; reason: the paper assumes the minimax theorem throughout (p.13), so the value exists and is unique
--   - encoding: (z, t) is a min-max strategy and (z, t, 0) is a max-min strategy → IsMinMaxStrategy … 0 and IsMaxMinStrategy … 0; reason: both strategies carry their value, which is v = 0 in this case (the proof: 'and v = 0')
--   - encoding: every max-min strategy (q, r, s) → IsMaxMinStrategy … q u for any u; reason: the published predicate carries the max-min value as an argument; no strategy is excluded
--   - encoding: C ∈ ℝ^{k×k}, k ≥ 1 → finite type ι with [Nonempty ι]; reason: no instance changes
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Theorem 8, p.21

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_StengelZeroSum_DM
import Definitions.Def_StengelZeroSum_IsMin58

open Matrix ZeroSumLP.DantzigExt

namespace StengelZeroSum

/-- **Theorem 8**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Theorem 8,
p.21. Let `C ∈ ℝ^{k×k}` with `C = −C⊤` and `d ∈ ℝ^k`. Let `(z*, w*)` minimize `w` subject to
(58) `Cz − 1w ≤ d, d⊤z − w ≤ 0, z ≥ 0, w ≥ 0`, and let `M ∈ ℝ` with (59) `1⊤z* + 1 ≤ M`.
Then the game `D_M` of (60) has a value, and every value `v` of `D_M` satisfies `v ≥ 0` and
(a) `v = 0` iff `w* = 0`; if `w* = 0`, with `t = 1/(1⊤z* + 1)` and `z = z* t`, `(z, t)` is a
min-max strategy and `(z, t, 0)` a max-min strategy of `D_M` (both with value 0);
(b) if `v > 0`, every max-min strategy `(q, r, s)` of `D_M` has `r = 0`, `s = v` and (61)
`Cq ≤ 0, d⊤q < 0`; and there is no `z ≥ 0` with `Cz ≤ d`.

**Formalization Note** The paper takes `(z*, w*)` to be a *basic* feasible minimizer; the
statement here holds for every minimizer (`IsMin58`), which includes the basic ones. Column
strategies `(z, t)` live on `ι ⊕ Unit`, row strategies `(q, r, s)` on `(ι ⊕ Unit) ⊕ Unit`
(see `DM`). `[Nonempty ι]` is `k ≥ 1`. -/
theorem theorem_8 {ι : Type*} [Fintype ι] [Nonempty ι] (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (d : ι → ℝ) (zs : ι → ℝ) (ws : ℝ) (hmin : IsMin58 C d zs ws) (M : ℝ)
    (hM : ∑ i, zs i + 1 ≤ M) :
    (∃ v, IsGameValue (DM C d M) v) ∧
    ∀ v, IsGameValue (DM C d M) v →
      0 ≤ v ∧
      -- (a)
      (v = 0 ↔ ws = 0) ∧
      (ws = 0 →
        IsMinMaxStrategy (DM C d M)
            (Sum.elim (fun i => zs i * (1 / (∑ i, zs i + 1))) fun _ => 1 / (∑ i, zs i + 1)) 0 ∧
          IsMaxMinStrategy (DM C d M)
            (Sum.elim (Sum.elim (fun i => zs i * (1 / (∑ i, zs i + 1)))
              fun _ => 1 / (∑ i, zs i + 1)) fun _ => 0) 0) ∧
      -- (b)
      (0 < v →
        (∀ (q : (ι ⊕ Unit) ⊕ Unit → ℝ) (u : ℝ), IsMaxMinStrategy (DM C d M) q u →
          q (.inl (.inr ())) = 0 ∧ q (.inr ()) = v ∧
          C *ᵥ (fun i => q (.inl (.inl i))) ≤ 0 ∧ d ⬝ᵥ (fun i => q (.inl (.inl i))) < 0) ∧
        ¬ ∃ z : ι → ℝ, 0 ≤ z ∧ C *ᵥ z ≤ d) := by sorry

end StengelZeroSum
