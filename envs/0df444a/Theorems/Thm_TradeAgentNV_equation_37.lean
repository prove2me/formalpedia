-- Prove2me | Theorems.Thm_TradeAgentNV_equation_37
-- name    : TradeAgentNV.equation_37
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:30:21.241998+00:00
-- url     : https://prove2.me/theorems/d42e4cdc-b3d8-47cb-95f7-52770a0a3a77
-- title:
--   Display (37): $D/q>h/\rho$ implies $E[\min(U,D/q)]/E[U]\ge E[\min(U,h/\rho)]/E[U]$ and $E[\min(U,D/q)]/E[U]>h/\rho$ (corrected: second inequality dropped)
-- statement:
--   Let $U$ be a random variable with $0\le U\le1$ almost surely and $E[U]>0$ (no other assumption on its law), let $D,r,t,h,\pi>0$ with $r-t+\pi>0$, $q>0$ and $\rho=r-t+h+\pi$. If $D/q>h/\rho$, then
--   $$
--   \frac{E[\min(U,D/q)]}{E[U]}\ge\frac{E[\min(U,h/\rho)]}{E[U]}\qquad\text{and}\qquad\frac{E[\min(U,D/q)]}{E[U]}>\frac h\rho .
--   $$
--   This is the step that gives Theorem 1(iv): a demand-to-supply ratio above the threshold makes bidding profitable.
--
--   Differences from the source:
--   - correction: the chain $E[\min(U,D/q)]/E[U]\ge E[\min(U,h/\rho)]/E[U]>h/\rho$ → the first inequality $E[\min(U,D/q)]/E[U]\ge E[\min(U,h/\rho)]/E[U]$ and the outer inequality $E[\min(U,D/q)]/E[U]>h/\rho$, without the second inequality; reason: the second inequality is false for yields Theorem 1 allows: for a Bernoulli $U$ with $P(U=1)=p\in(0,1)$, $E[\min(U,s)]=sE[U]$ for $s\in[0,1]$ (Lemma 2 needs a continuous $U$); the outer inequality holds for every admissible $U$
--   - encoding: the seller has $q$ units ($D/q$ is used throughout) → $q>0$; reason: implicit in the paper; $D/q$ is undefined at $q=0$
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, proof of Theorem 1(iv), display (37), p.29

import Mathlib
import Definitions.Def_TradeAgentNV_rho
import Definitions.Def_TradeAgentNV_salesSupplyRatio

open MeasureTheory

namespace TradeAgentNV

/-- **Display (37), corrected** (proof of Theorem 1(iv), p.29) of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023):
if the demand-to-supply ratio exceeds the threshold, `D/q > h/ρ`, then
`E[min(U, D/q)]/E[U] ≥ E[min(U, h/ρ)]/E[U]` (the first inequality of (37)) and the expected
sales-to-supply ratio exceeds the threshold too: `E[min(U, D/q)]/E[U] > h/ρ`.

**Formalization Note.** `0 ≤ U ≤ 1` a.s. and `E[U] > 0` (p.9) with no further assumption on the
law of `U`; `D, r, t, h, π > 0`, `r − t + π > 0` (p.8) and `q > 0`. The paper's
second inequality `E[min(U, h/ρ)]/E[U] > h/ρ` is not stated: it fails for a Bernoulli `U` (then `E[min(U, s)] = sE[U]` for `s ∈ [0, 1]`). -/
theorem equation_37
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π) :
    h / rho r t h π < D / q →
      (∫ ω, min (U ω) (h / rho r t h π) ∂P) / (∫ ω, U ω ∂P) ≤ salesSupplyRatio P U D q ∧
        h / rho r t h π < salesSupplyRatio P U D q := by sorry

end TradeAgentNV
