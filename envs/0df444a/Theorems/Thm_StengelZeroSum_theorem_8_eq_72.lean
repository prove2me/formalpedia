-- Prove2me | Theorems.Thm_StengelZeroSum_theorem_8_eq_72
-- name    : StengelZeroSum.theorem_8_eq_72
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:41.596945+00:00
-- url     : https://prove2.me/theorems/0aeaf399-6edc-41da-916d-71abc2828afd
-- title:
--   (67), (72) — if $v>0$ then $v<1$ and $w^*=(M+1)/(1/v-1)$
-- statement:
--   Under the hypotheses of Theorem 8 ($C=-C^\top$, $(z^*,w^*)$ minimizes $w$ subject to (58), and $\mathbf1^\top z^*+1\le M$ (59)), let $v$ be the value of the game $D_M$ of (60) and suppose $v>0$. Then $v<1$, every min-max strategy $(z,t)$ of $D_M$ has $t=(1-v)/(M+1)>0$ (67), and
--
--   $$
--   w^*=\frac{M+1}{1/v-1}.\qquad(72)
--   $$
--
--   The proof of Theorem 8 obtains $0<v\le s<1$ before (67) and the identity (72) from the chain of inequalities (71). Theorem 7(b) uses $v<1$ and, through the least relaxation of (53), the formula (54).
--
--   **Formalization Note** As in Theorem 8, the minimizer need not be basic.
--
--   Differences from the source:
--   - generalization: (z*, w*) a basic feasible minimizer of (58) → (z*, w*) any minimizer of (58); reason: the derivation of (67)–(72) never uses basicness; basic minimizers are a special case
--   - encoding: C ∈ ℝ^{k×k}, k ≥ 1 → finite type ι with [Nonempty ι]; reason: no instance changes
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, proof of Theorem 8, eqs. (67) and (72), pp.22–23

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame
import Definitions.Def_StengelZeroSum_DM
import Definitions.Def_StengelZeroSum_IsMin58

open Matrix ZeroSumLP.DantzigExt

namespace StengelZeroSum

/-- **The value formula (67)/(72) of the proof of Theorem 8**,
von Stengel, *Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, proof of
Theorem 8, pp.22–23: "Hence, 0 < v ≤ s < 1 and by (65), t = (1 − v)/(M + 1) > 0 (67)" and
"Hence, all inequalities hold as equalities, in particular w* = (M + 1)/(1/v − 1) (72)".

Under the hypotheses of Theorem 8 (`C = −C⊤`, `(z*, w*)` minimizes `w` subject to (58),
`1⊤z* + 1 ≤ M` (59)), if the value `v` of `D_M` (60) is positive then `v < 1`, every min-max
strategy `(z, t)` of `D_M` has `t = (1 − v)/(M + 1) > 0`, and `w* = (M + 1)/(1/v − 1)`.

**Formalization Note** As in `theorem_8`, `(z*, w*)` is any minimizer of (58), not only a
basic one. `[Nonempty ι]` is `k ≥ 1`. -/
theorem theorem_8_eq_72 {ι : Type*} [Fintype ι] [Nonempty ι] (C : Matrix ι ι ℝ)
    (hC : Cᵀ = -C) (d : ι → ℝ) (zs : ι → ℝ) (ws : ℝ) (hmin : IsMin58 C d zs ws) (M : ℝ)
    (hM : ∑ i, zs i + 1 ≤ M) (v : ℝ) (hv : IsGameValue (DM C d M) v) (hpos : 0 < v) :
    v < 1 ∧
      (∀ z : ι ⊕ Unit → ℝ, IsMinMaxStrategy (DM C d M) z v →
        z (.inr ()) = (1 - v) / (M + 1) ∧ 0 < z (.inr ())) ∧
      ws = (M + 1) / (1 / v - 1) := by sorry

end StengelZeroSum
