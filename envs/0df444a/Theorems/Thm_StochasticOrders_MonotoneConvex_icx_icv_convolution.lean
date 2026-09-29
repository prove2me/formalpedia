-- Prove2me | Theorems.Thm_StochasticOrders_MonotoneConvex_icx_icv_convolution
-- name    : StochasticOrders.MonotoneConvex.icx_icv_convolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:01.579618+00:00
-- url     : https://prove2.me/theorems/d09565f4-5837-4837-a258-1a976e21505e
-- title:
--   Theorem 4.A.8(d) — closure of the increasing convex/concave orders under convolution
-- statement:
--   Let $X_1,\dots,X_m$ be independent random variables on $(\Omega,\mu)$ and let
--   $Y_1,\dots,Y_m$ be another independent family, on $(\Omega',\nu)$. Then
--
--   $$\text{if } X_i \le_{icx} Y_i \text{ for every } i,\ \text{then } \sum_i X_i \le_{icx}
--     \sum_i Y_i;$$
--   $$\text{if } X_i \le_{icv} Y_i \text{ for every } i,\ \text{then } \sum_i X_i \le_{icv}
--     \sum_i Y_i:$$
--
--   both the increasing convex and increasing concave orders are closed under convolutions — the
--   direct analogue, for this chapter's orders, of Chunk 03's Theorem 3.A.12(d) closure of the
--   plain convex order (the book notes the last two parts of its own Theorem 4.A.8, including
--   this one, "can be proven as in Theorem 3.A.12").
--
--   **Formalization Note** Drafted as a single Lean theorem with two independent implication
--   conjuncts (`(icx hyp → icx concl) ∧ (icv hyp → icv concl)`, not an `Or`), since the book
--   states both cases as the two bracketed halves of one theorem sharing the same independence
--   hypotheses on the two families. Independence is Mathlib's `ProbabilityTheory.iIndepFun`, one
--   family per side, matching Chunk 03's convention for its own Theorem 3.A.12(d) milestone.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 186, Theorem 4.A.8(d)

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

namespace StochasticOrders.MonotoneConvex

open MeasureTheory ProbabilityTheory

/-- Theorem 4.A.8(d) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 186): let
`X₁, …, Xₘ` be independent random variables and `Y₁, …, Yₘ` another independent family. If
`Xᵢ ≤icx Yᵢ` for every `i`, then `∑ᵢ Xᵢ ≤icx ∑ᵢ Yᵢ`; and if `Xᵢ ≤icv Yᵢ` for every `i`, then
`∑ᵢ Xᵢ ≤icv ∑ᵢ Yᵢ`: both the increasing convex and increasing concave orders are closed under
convolutions. -/
theorem icx_icv_convolution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (X : Fin m → Ω → ℝ) (Y : Fin m → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν) :
    ((∀ i, IcxOrder μ ν (X i) (Y i)) →
      IcxOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω))
    ∧
    ((∀ i, IcvOrder μ ν (X i) (Y i)) →
      IcvOrder μ ν (fun ω => ∑ i, X i ω) (fun ω => ∑ i, Y i ω)) := by sorry

end StochasticOrders.MonotoneConvex
