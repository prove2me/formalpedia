-- Prove2me | Theorems.Thm_PELiquidity_Secondary_discount_bounds
-- name    : PELiquidity.Secondary.discount_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:03.426145+00:00
-- url     : https://prove2.me/theorems/91ad9e79-a74c-4b32-b266-98d8a5ccb6ef
-- title:
--   §6.1: traded claims have bounded discount
-- statement:
--   In a secondary-market equilibrium where a positive quantity of L-fund claims is traded, the claim price cannot lie below the L sellers' reservation value or above the H buyers' reservation value. Consequently,
--   $$
--   1-\delta_H\leq D_L=1-\frac{P_L}{\bar R_{PE,L}}\leq1-\delta_L.
--   $$
--   These bounds determine the discount range used in Lemma 3 and the equilibrium characterization.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), pp. 26–27, following (21)

import Mathlib
import Definitions.Def_PELiquidity_Secondary_Market

namespace PELiquidity.Secondary

theorem discount_bounds (P : PELiquidity.Primary.Params) (muH : ℝ) (E : AllocationSec)
    (hEq : IsEquilibriumSec P muH E) (hTrade : 0 < E.sL) :
    1 - P.δH ≤ discount E ∧ discount E ≤ 1 - P.δL := by sorry

end PELiquidity.Secondary
