-- Prove2me | Theorems.Thm_PELiquidity_Secondary_eq_C5
-- name    : PELiquidity.Secondary.eq_C5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:26.891744+00:00
-- url     : https://prove2.me/theorems/14007d67-b4da-41e9-a95d-1232f5758d6e
-- title:
--   (C.5): minimum L-LP primary-market return
-- statement:
--   Let $\lambda\in(0,1)$ be the liquidity-shock probability, and let $D_L$ lie between $1-\delta_H$ and $1-\delta_L$. For any proposed L-fund return $\bar R$, the L-LP indifference equation is equivalent to
--   $$
--   \bar R[1-\lambda+\lambda(1-D_L)]=1
--   \quad\Longleftrightarrow\quad
--   \bar R=\frac1{1-\lambda D_L}=1+\frac{\lambda D_L}{1-\lambda D_L}.
--   $$
--   This identifies the minimum primary-market return acceptable to L-LPs at a given secondary-market discount.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 49, Appendix C.5, (C.5)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Secondary

theorem eq_C5 (P : PELiquidity.Primary.Params) (D Rb : ℝ)
    (hDlo : 1 - P.δH ≤ D) (hDhi : D ≤ 1 - P.δL) :
    (Rb * (1 - P.lam + P.lam * (1 - D)) = 1 ↔
      Rb = 1 / (1 - P.lam * D)) ∧
    1 / (1 - P.lam * D) = 1 + P.lam * D / (1 - P.lam * D) := by sorry

end PELiquidity.Secondary
