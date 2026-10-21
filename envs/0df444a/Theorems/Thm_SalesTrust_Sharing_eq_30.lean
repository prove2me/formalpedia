-- Prove2me | Theorems.Thm_SalesTrust_Sharing_eq_30
-- name    : SalesTrust.Sharing.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:19.158067+00:00
-- url     : https://prove2.me/theorems/1cc0cef0-e5be-4832-93d5-5f7befa9d10a
-- title:
--   (30), Online Supplement p. 7 — the retailer's expected profit with past sales information
-- statement:
--   Under the standing assumptions, the retailer's expected per-period profit at the sharing menu of Proposition 2 is
--   $$\Pi^{D,e}_R = \frac{p(V_H - V_L)(V_L - pV_H)}{2(1-p)(1+\delta p)^2} + \frac{\delta p^2 (V_H - V_L)}{2(1-p)(1+\delta p)^2}\Big((1 - p - \delta(1 + p + p^2))V_H + (1 + \delta - p + 2\delta p)V_L\Big).$$
--
--   This is the sharing side of the comparison in Proposition 3.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), proof of Proposition 3, Online Supplement p. 7 (PDF 41), (30)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- (30), Online Supplement p. 7: the retailer's expected profit at the sharing menu. -/
theorem eq_30 (P : Params) (hS : P.Standing) :
    retailerProfit P (menuE P) =
      P.p * (P.VH - P.VL) * (P.VL - P.p * P.VH) / (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) +
        P.δ * P.p ^ 2 * (P.VH - P.VL) / (2 * (1 - P.p) * (1 + P.δ * P.p) ^ 2) *
          ((1 - P.p - P.δ * (1 + P.p + P.p ^ 2)) * P.VH +
            (1 + P.δ - P.p + 2 * P.δ * P.p) * P.VL) := by sorry

end SalesTrust.Sharing
