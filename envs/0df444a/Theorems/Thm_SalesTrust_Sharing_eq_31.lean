-- Prove2me | Theorems.Thm_SalesTrust_Sharing_eq_31
-- name    : SalesTrust.Sharing.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:03.612993+00:00
-- url     : https://prove2.me/theorems/368d7d18-0e6d-4d19-b37b-63039b0efd74
-- title:
--   (31), Online Supplement p. 7 — Π^{D,e}_R − Π^{D,ne}_R = δp³(1−δ)(V_H−V_L)²/(2(1−p)(1+δp)²)·[1 − δ(2+δp)]
-- statement:
--   Under the standing assumptions, the difference between the retailer's expected per-period profits at the sharing menu of Proposition 2 and at the no-sharing menu of Proposition 1 is
--   $$\Pi^{D,e}_R - \Pi^{D,ne}_R = \frac{\delta p^3 (1-\delta)(V_H - V_L)^2}{2(1-p)(1+\delta p)^2}\,\big[1 - \delta(2 + \delta p)\big].$$
--
--   The prefactor is nonnegative, so the sign of the gap is the sign of $1 - \delta(2+\delta p)$; this is the computation behind Proposition 3.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), proof of Proposition 3, Online Supplement p. 7 (PDF 41), (31)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- (31), Online Supplement p. 7: the gap in the retailer's expected profit with and
without sales information. -/
theorem eq_31 (P : Params) (hS : P.Standing) :
    retailerProfit P (menuE P) - retailerProfit P (menuNE P) =
      P.δ * P.p ^ 3 * (1 - P.δ) * (P.VH - P.VL) ^ 2 / (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) *
        (1 - P.δ * (2 + P.δ * P.p)) := by sorry

end SalesTrust.Sharing
