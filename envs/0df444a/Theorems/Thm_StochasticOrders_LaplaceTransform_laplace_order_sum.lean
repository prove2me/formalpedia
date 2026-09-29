-- Prove2me | Theorems.Thm_StochasticOrders_LaplaceTransform_laplace_order_sum
-- name    : StochasticOrders.LaplaceTransform.laplace_order_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:50.413249+00:00
-- url     : https://prove2.me/theorems/b6eae39b-a2c9-492d-9f5d-2493885241f4
-- title:
--   Theorem 5.A.7(d) — closure under convolutions
-- statement:
--   Let $X_1,\dots,X_m$ be independent random variables on $(\Omega,\mu)$ and let $Y_1,\dots,Y_m$
--   be another independent family, on $(\Omega',\nu)$. If $X_i \le_{Lt} Y_i$ for every $i =
--   1,\dots,m$, then
--
--   $$\sum_{i=1}^m X_i \le_{Lt} \sum_{i=1}^m Y_i.$$
--
--   This is the "in particular" corollary of the chapter's general closure theorem (5.A.7(d)),
--   which allows any nonnegative $g$ on $[0,\infty)^m$ whose partial derivative in each coordinate
--   is completely monotone in that coordinate; taking $g$ to be the coordinate sum recovers this
--   convolution closure, the fact that gives the order its role in comparing sums of independent
--   nonnegative risks, exactly as for the usual stochastic order in Chapter 1.
--
--   **Formalization Note** Drafted as its own theorem (the convolution special case), per the
--   book's own two-sentence presentation ("... for all such $g$ ... In particular, the Laplace
--   transform order is closed under convolutions"), matching how Chunk 01 drafted its convolution
--   corollary (`usual_order_sum`) rather than the fully general multivariable-$g$ statement.
--   Independence of each family is `ProbabilityTheory.iIndepFun`, one family per side.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 236, Theorem 5.A.7(d)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder

namespace StochasticOrders.LaplaceTransform

open MeasureTheory ProbabilityTheory

/-- Theorem 5.A.7(d), convolution corollary (Shaked & Shanthikumar, *Stochastic Orders*, Springer
2007, p. 236): let `X_1, …, X_m` be independent random variables and `Y_1, …, Y_m` another
independent family. If `X_i ≤Lt Y_i` for every `i`, then `∑ᵢ X_i ≤Lt ∑ᵢ Y_i`: the Laplace transform
order is closed under convolutions. -/
theorem laplace_order_sum {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXnn : ∀ i ω, 0 ≤ X i ω) (hYnn : ∀ i ω, 0 ≤ Y i ω)
    (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, LaplaceOrder μ ν (X i) (Y i)) :
    LaplaceOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω) := by sorry

end StochasticOrders.LaplaceTransform
