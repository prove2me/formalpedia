-- Prove2me | Theorems.Thm_PELiquidity_Secondary_eq_C10
-- name    : PELiquidity.Secondary.eq_C10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:04.542844+00:00
-- url     : https://prove2.me/theorems/68ac065a-1700-4a28-b796-681ba6898c2c
-- title:
--   (C.10): interior secondary-market clearing
-- statement:
--   Consider a secondary-market equilibrium with no H-funds and an interior L-claim discount $1-\delta_H<D_L<1-\delta_L$. L-LPs then sell all their primary-market claims and H-LPs spend their available capital on them. Market clearing gives
--   $$
--   (I_L-A)P_L=\mu_H K.
--   $$
--   This equation pins down the discount in the interior trading regime.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 51, Appendix C.6, Case 3, (C.10)

import Mathlib
import Definitions.Def_PELiquidity_Secondary_Market

namespace PELiquidity.Secondary

theorem eq_C10 (P : PELiquidity.Primary.Params) (muH : ℝ) (E : AllocationSec)
    (hEq : IsEquilibriumSec P muH E) (hNoH : E.αH = 0)
    (hDlo : 1 - P.δH < discount E)
    (hDhi : discount E < 1 - P.δL) :
    (E.IL - P.A) * E.PL = muH * P.K := by sorry

end PELiquidity.Secondary
