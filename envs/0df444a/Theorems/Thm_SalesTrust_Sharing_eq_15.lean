-- Prove2me | Theorems.Thm_SalesTrust_Sharing_eq_15
-- name    : SalesTrust.Sharing.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:14.797474+00:00
-- url     : https://prove2.me/theorems/8bc4a8a6-7131-4e1f-8cc1-a1dbc2be1f60
-- title:
--   (15), p. 13 — the retailer's expected profit without sales information
-- statement:
--   Under the standing assumptions, the retailer's expected per-period profit at the no-sharing menu of Proposition 1 is
--   $$\Pi^{D,ne}_R = \frac{p(V_H - V_L)(V_L - pV_H)}{2(1-p)} + \delta(1-\delta)\,\frac{p^2(V_H - V_L)^2}{2(1-p)},$$
--   and the first term is the static profit, $\Pi^S_R = p\Delta(q^S_L) = \dfrac{p(V_H - V_L)(V_L - pV_H)}{2(1-p)}$.
--
--   This is the no-sharing side of the comparison in Proposition 3.
-- source:
--   Shamir & Yehezkel, Sales information transparency and trust in repeated vertical relationships, authors' manuscript (January 2023; MSOM, DOI 10.1287/msom.2023.1208), p. 13 (PDF 14), (15)

import Mathlib
import Definitions.Def_SalesTrust_Sharing_Model

namespace SalesTrust.Sharing

/-- (15), p. 13: the retailer's expected profit at the no-sharing menu. -/
theorem eq_15 (P : Params) (hS : P.Standing) :
    retailerProfit P (menuNE P) =
        P.p * (P.VH - P.VL) * (P.VL - P.p * P.VH) / (2 * (1 - P.p)) +
          P.δ * (1 - P.δ) * (P.p ^ 2 * (P.VH - P.VL) ^ 2 / (2 * (1 - P.p))) ∧
      staticRent P = P.p * (P.VH - P.VL) * (P.VL - P.p * P.VH) / (2 * (1 - P.p)) := by sorry

end SalesTrust.Sharing
