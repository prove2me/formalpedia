-- Prove2me | Theorems.Thm_StochasticOrders_Usual_usual_order_convolution
-- name    : StochasticOrders.Usual.usual_order_convolution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:32:24.026984+00:00
-- url     : https://prove2.me/theorems/a8208567-b950-4dc8-a0da-eb915fea422c
-- title:
--   Theorem 1.A.3(b) — closure under increasing functions of independent families and convolution
-- statement:
--   Let $X_1,\dots,X_m$ be independent random variables on $(\Omega,\mu)$ and let
--   $Y_1,\dots,Y_m$ be another independent family, on $(\Omega',\nu)$. If $X_i \le_{st} Y_i$ for
--   every $i = 1,\dots,m$, then for any increasing function $\psi : \mathbb{R}^m \to \mathbb{R}$,
--
--   $$\psi(X_1,\dots,X_m) \le_{st} \psi(Y_1,\dots,Y_m).$$
--
--   In particular, taking $\psi(x) = \sum_i x_i$ (itself increasing),
--   $\sum_i X_i \le_{st} \sum_i Y_i$: the usual stochastic order is closed under convolutions —
--   the corollary that gives the order its central role in comparing sums of independent risks,
--   waiting times, and workloads throughout the book.
--
--   **Formalization Note** Two theorems are drafted: the general statement
--   (`usual_order_convolution`, for any monotone $\psi : (\text{Fin } m \to \mathbb{R}) \to
--   \mathbb{R}$) and the convolution corollary (`usual_order_sum`) as its own theorem rather than a
--   derived one-liner, per the book's own presentation of both. Independence is formalized via
--   Mathlib's `ProbabilityTheory.iIndepFun`.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 6, Theorem 1.A.3(b)

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace StochasticOrders.Usual

open MeasureTheory ProbabilityTheory

/-- Theorem 1.A.3(b) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 6): let
`X_1, …, X_m` be independent random variables and `Y_1, …, Y_m` another independent family. If
`X_i ≤st Y_i` for every `i`, then for any increasing function `ψ : ℝᵐ → ℝ`,
`ψ(X_1, …, X_m) ≤st ψ(Y_1, …, Y_m)`. In particular (taking `ψ = ∑ᵢ xᵢ`, itself increasing),
`∑ᵢ X_i ≤st ∑ᵢ Y_i`: the usual stochastic order is closed under convolutions. -/
theorem usual_order_convolution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, UsualOrder μ ν (X i) (Y i)) (ψ : (Fin m → ℝ) → ℝ) (hψ : Monotone ψ) :
    UsualOrder μ ν (fun ω => ψ (fun i => X i ω)) (fun ω => ψ (fun i => Y i ω)) := by sorry

end StochasticOrders.Usual
