-- Prove2me | Theorems.Thm_TradeAgentNV_equation_8
-- name    : TradeAgentNV.equation_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:02.208906+00:00
-- url     : https://prove2.me/theorems/be4710d5-5bde-445b-9057-fce0041ebc9b
-- title:
--   Display (8): $R>0$ iff the expected sales-to-supply ratio exceeds $h/\rho$
-- statement:
--   Let $U$ be a random variable with $0\le U\le1$ almost surely and $E[U]>0$, let $D,r,t,h,\pi>0$ with $r-t+\pi>0$, $q>0$, $\rho=r-t+h+\pi$ and $R=\rho E[\min(qU,D)]-hqE[U]$. Then
--   $$
--   R>0\iff\frac{E[\min(qU,D)]}{qE[U]}>\frac h\rho\iff\frac{E[\min(U,D/q)]}{E[U]}>\frac h\rho .
--   $$
--   So the conditions of Theorem 1(i) and (ii) are $R\le0$ and $R>0$.
--
--   Differences from the source:
--   - encoding: the seller has $q$ units ($D/q$ is used throughout) → $q>0$; reason: implicit in the paper; $D/q$ is undefined at $q=0$
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, display (8), p.11

import Mathlib
import Definitions.Def_TradeAgentNV_expBenefit
import Definitions.Def_TradeAgentNV_salesSupplyRatio

open MeasureTheory

namespace TradeAgentNV

/-- **Display (8)** (p.11) of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023): the expected benefit of bidding
`R = ρE[min(qU, D)] − hqE[U]` is positive exactly when the expected sales-to-supply ratio
exceeds `h/ρ`, in either of its two forms:
`R > 0 ⇔ E[min(qU, D)]/(qE[U]) > h/ρ ⇔ E[min(U, D/q)]/E[U] > h/ρ`.

**Formalization Note.** `0 ≤ U ≤ 1` a.s. and `E[U] > 0` (p.9); `D, r, t, h, π > 0`,
`r − t + π > 0` (p.8) and `q > 0`; so `ρ`, `qE[U]` and `E[U]` are positive. -/
theorem equation_8
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π) :
    (0 < expBenefit P U r t h π D q ↔
        h / rho r t h π < (∫ ω, min (q * U ω) D ∂P) / (q * ∫ ω, U ω ∂P)) ∧
      (h / rho r t h π < (∫ ω, min (q * U ω) D ∂P) / (q * ∫ ω, U ω ∂P) ↔
        h / rho r t h π < salesSupplyRatio P U D q) := by sorry

end TradeAgentNV
