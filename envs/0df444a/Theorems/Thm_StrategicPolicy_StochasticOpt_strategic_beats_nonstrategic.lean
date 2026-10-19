-- Prove2me | Theorems.Thm_StrategicPolicy_StochasticOpt_strategic_beats_nonstrategic
-- name    : StrategicPolicy.StochasticOpt.strategic_beats_nonstrategic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:00:33.196502+00:00
-- url     : https://prove2.me/theorems/9b66e503-79e4-44b7-ae47-b90e483e8bdc
-- title:
--   §3, p. 5, example after (8) — the strategic optimum's utility exceeds that of its non-strategic counterpart
-- statement:
--   In the three-value instance of §3, let $\pi^*=(1,0.7,0)$ and let $\mathbf 1=(1,1,1)$ be the non-strategic optimum. Then
--   $$
--   u_{\mathrm{NS}}(\mathbf 1,\gamma)<u(\pi^*,\gamma)\qquad\text{and}\qquad u(\mathbf 1,\gamma)<u(\pi^*,\gamma),
--   $$
--   where $u$ is the strategic utility (7) and $u_{\mathrm{NS}}$ the non-strategic utility.
--
--   The paper's "counterpart in the non-strategic setting" admits two readings: the non-strategic optimum evaluated without strategic behaviour, or the same policy deployed in the strategic setting. Both comparisons are stated.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 5, §3, example after (8), last sentence

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example

namespace StrategicPolicy.StochasticOpt

theorem strategic_beats_nonstrategic :
    uNS p0 q0 γ0 (fun _ => 1) < u p0 q0 γ0 c0 ![1, 7 / 10, 0] ∧
      u p0 q0 γ0 c0 (fun _ => 1) < u p0 q0 γ0 c0 ![1, 7 / 10, 0] := by sorry

end StrategicPolicy.StochasticOpt
