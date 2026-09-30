-- Prove2me | Theorems.Thm_RevenueManagement_rm_duopoly_littlewood_monotone
-- name    : RevenueManagement.rm_duopoly_littlewood_monotone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:03:37.977898+00:00
-- url     : https://prove2.me/theorems/23ef3909-acb7-4f8e-a2e6-a02a14421521
-- title:
--   Proposition 8.1: in the RM duopoly game a firm's Littlewood protection level is nonincreasing in its rival's protection level, so its equilibrium graph has no crossing arcs
-- statement:
--   For any high-fare demands $D_1, D_2$ on a probability space and fares $p_H \ge 0$, $p_L$,
--   if the rival protects more ($y_2 \le y_2'$) then a firm's Littlewood protection level against
--   the effective demand $D_1 + (D_2 - y_2')^+$ is at most its level against
--   $D_1 + (D_2 - y_2)^+$. In the book's indexing, where firm 2's node $j$ means protecting
--   $C - j$ units, this says the best-response arcs $(k_2, k_1)$, $(l_2, l_1)$ with
--   $l_2 > k_2$ never have $l_1 < k_1$: no crossing arcs.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 381, Proposition 8.1 (proof in Appendix 8.A p. 404: 'If firm 2 chooses l2 (that is, protects less for its H demand), then firm 1 should see more of a spillover of firm 2 H demand ... So by Littlewood's rule, its protection level should increase')

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem rm_duopoly_littlewood_monotone (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (D1 D2 : Ω → ℕ)
    (pL pH : ℝ) (hpH : 0 ≤ pH) (C y2 y2' : ℕ) (h : y2 ≤ y2') :
    littlewoodResponse P (spilloverDemand D1 D2 y2') pL pH C ≤
      littlewoodResponse P (spilloverDemand D1 D2 y2) pL pH C := by sorry

end RevenueManagement
