-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_cond12_always
-- name    : VerticalOwnership.CheapTalk.cond12_always
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:33.27313+00:00
-- url     : https://prove2.me/theorems/92a99445-78a7-4fe5-828f-366af5da4674
-- title:
--   §5, p. 13 — condition (12) is always satisfied: the high type never gains by reporting low
-- statement:
--   In the model of the mission, for every ownership share $\beta\in[0,1]$, condition (12) holds:
--   $$v_r\big(0,\mu_H+F^{-1}(z_s)\,\big|\,\mu_H\big)\ \ge\ v_r\big(0,\mu_L+F^{-1}(z_s)\,\big|\,\mu_H\big).$$
--   That is, when demand is high, the retailer's accounting payoff from truthfully reporting the high state (so that the supplier builds $K_H$) is at least her payoff from claiming the low state (so that the supplier builds $K_L$).
--
--   Consequently the possibility of truthful cheap talk hinges on condition (13) alone.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 13, §5, after (13); proof p. 45, Appendix E, Proof of Theorem 2(i)

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem cond12_always (M : Model) (hM : M.Standing) :
    ∀ β ∈ Set.Icc (0 : ℝ) 1, M.cond12 β := by sorry

end VerticalOwnership.CheapTalk
