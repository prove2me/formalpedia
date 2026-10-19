-- Prove2me | Theorems.Thm_PELiquidity_Secondary_eq_C6
-- name    : PELiquidity.Secondary.eq_C6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:19.165806+00:00
-- url     : https://prove2.me/theorems/56a40026-52be-4e80-9248-ccdc0c9defcd
-- title:
--   (C.6): minimum H-LP primary-market return
-- statement:
--   For a discount $D_L\in[1-\delta_H,1-\delta_L]$, let $\bar R$ be a proposed H-fund return. Indifference between cash and the H-fund is equivalent to
--   $$
--   1-\lambda+\frac{\lambda\delta_H}{1-D_L}
--   =\bar R(1-\lambda+\lambda\delta_H)
--   \quad\Longleftrightarrow\quad
--   \bar R=1+\frac{\lambda\delta_H D_L}{1-D_L}
--   \frac1{1-\lambda(1-\delta_H)}.
--   $$
--   This return incorporates the H-LPs' opportunity to purchase discounted L-claims after a liquidity shock.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 49, Appendix C.5, (C.6)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Secondary

theorem eq_C6 (P : PELiquidity.Primary.Params) (D Rb : ℝ)
    (hDlo : 1 - P.δH ≤ D) (hDhi : D ≤ 1 - P.δL) :
    (1 - P.lam + P.lam * P.δH / (1 - D) =
      Rb * (1 - P.lam + P.lam * P.δH) ↔
      Rb = 1 + P.lam * P.δH * D / (1 - D) * PELiquidity.Primary.grossReturn P.lam P.δH) := by sorry

end PELiquidity.Secondary
