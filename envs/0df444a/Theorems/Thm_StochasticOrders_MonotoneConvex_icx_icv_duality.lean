-- Prove2me | Theorems.Thm_StochasticOrders_MonotoneConvex_icx_icv_duality
-- name    : StochasticOrders.MonotoneConvex.icx_icv_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T22:58:56.438916+00:00
-- url     : https://prove2.me/theorems/353690c0-222c-4a82-baf7-ed7fa5d96157
-- title:
--   Theorem 4.A.1 — duality between the increasing convex and increasing concave orders
-- statement:
--   Let $X$ and $Y$ be two random variables. Then
--
--   $$X \le_{icx} Y \iff -X \ge_{icv} -Y, \qquad X \le_{icv} Y \iff -X \ge_{icx} -Y.$$
--
--   The proof rests on the fact that $\varphi(x)$ is increasing and convex in $x$ if, and only
--   if, $-\varphi(-x)$ is increasing and concave in $x$ — the book omits the "straightforward
--   details." This is the increasing-order analogue of Theorem 3.A.12(a)'s duality for the plain
--   convex order.
--
--   **Formalization Note** "$-X \ge_{icv} -Y$" is unfolded as its definition, "$-Y \le_{icv}
--   -X$" — the reversed order on the negated variables, stated as a genuine `IcvOrder` predicate
--   applied to `fun ω => -(Y ω)` and `fun ω => -(X ω)` (on the swapped measures, since $-Y$ lives
--   on $(\Omega',\nu)$ and $-X$ on $(\Omega,\mu)$), not a definitional unfolding that would make
--   the equivalence trivial by `simp`. Both bracketed cases of the book's single statement are
--   drafted as two conjuncts of one Lean theorem (not an `Or`), since each is an independently
--   meaningful equivalence between the two, separately-defined orders.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 182, Theorem 4.A.1

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory

/-- Theorem 4.A.1 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 182): let `X` and
`Y` be two random variables. Then `X ≤icx Y ⟺ −X ≥icv −Y` and `X ≤icv Y ⟺ −X ≥icx −Y`. The "≥"
direction is unfolded as the reversed order on the negated variables: `−X ≥icv −Y` means
`−Y ≤icv −X`, and likewise for the second equivalence. -/
theorem icx_icv_duality {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) :
    (IcxOrder μ ν X Y ↔ IcvOrder ν μ (fun ω => -(Y ω)) (fun ω => -(X ω))) ∧
    (IcvOrder μ ν X Y ↔ IcxOrder ν μ (fun ω => -(Y ω)) (fun ω => -(X ω))) := by sorry

end StochasticOrders.MonotoneConvex
