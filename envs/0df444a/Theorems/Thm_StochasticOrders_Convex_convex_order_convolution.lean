-- Prove2me | Theorems.Thm_StochasticOrders_Convex_convex_order_convolution
-- name    : StochasticOrders.Convex.convex_order_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:34.39667+00:00
-- url     : https://prove2.me/theorems/7506be42-d0de-4d56-9e07-9a5c50bc5852
-- title:
--   Theorem 3.A.12(d) — closure of the convex order under convolution
-- statement:
--   Let $X_1,\dots,X_m$ be independent random variables on $(\Omega,\mu)$ and let
--   $Y_1,\dots,Y_m$ be another independent family, on $(\Omega',\nu)$. If $X_i \le_{cx} Y_i$ for
--   every $i=1,\dots,m$, then
--
--   $$\sum_i X_i \le_{cx} \sum_i Y_i:$$
--
--   the convex order is closed under convolutions — the direct analogue, for variability rather
--   than location, of Chapter I's Theorem 1.A.3(b) closure of the usual stochastic order.
--
--   **Formalization Note** Unlike Theorem 1.A.3(b), the book states only the additive/convolution
--   case for the convex order here (not a general increasing-$\psi$ statement — a convex function
--   of independent convex-ordered sums need not itself be compatible with a general $\psi$ the way
--   the usual order's monotone-composition closure is), so only the sum is drafted, matching the
--   book's own Theorem 3.A.12(d) exactly. Independence is Mathlib's `ProbabilityTheory.iIndepFun`,
--   one family per side, as in Chapter I.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 120, Theorem 3.A.12(d)

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

namespace StochasticOrders.Convex

open MeasureTheory ProbabilityTheory

/-- Theorem 3.A.12(d) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 120): let
`X_1, …, X_m` be independent random variables and `Y_1, …, Y_m` another independent family. If
`X_i ≤cx Y_i` for every `i`, then `∑_i X_i ≤cx ∑_i Y_i`: the convex order is closed under
convolutions. -/
theorem convex_order_convolution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, ConvexOrder μ ν (X i) (Y i)) :
    ConvexOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω) := by sorry

end StochasticOrders.Convex
