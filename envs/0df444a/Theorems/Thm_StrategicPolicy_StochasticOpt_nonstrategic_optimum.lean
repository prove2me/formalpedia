-- Prove2me | Theorems.Thm_StrategicPolicy_StochasticOpt_nonstrategic_optimum
-- name    : StrategicPolicy.StochasticOpt.nonstrategic_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T13:00:29.299275+00:00
-- url     : https://prove2.me/theorems/e9c924b8-83ae-4817-93a2-94087e6d3587
-- title:
--   §3, p. 5, example after (8) — the non-strategic optimum is the threshold policy π = (1, 1, 1)
-- statement:
--   In the three-value instance of §3, consider the non-strategic utility, in which individuals do not change their features:
--   $$
--   u_{\mathrm{NS}}(\pi,\gamma)=\sum_{x=1}^{3}P(x)\,\bigl(P(y=1\mid x)-\gamma\bigr)\,\pi(x).
--   $$
--   A policy $\pi$ with values in $[0,1]$ maximizes $u_{\mathrm{NS}}$ over all such policies if and only if $\pi(x)=1$ for $x=1,2,3$.
--
--   Since every $P(y=1\mid x)$ exceeds $\gamma=0.1$, this is the deterministic threshold rule (8), and it is the unique non-strategic optimum.
--
--   **Formalization Note** Optimality is `IsMaxOn` over the whole set of policies $[0,1]^3$.
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 5, §3, example after (8), first sentence after the cost matrix

import Mathlib
import Definitions.Def_StrategicPolicy_StochasticOpt_Setting
import Definitions.Def_StrategicPolicy_StochasticOpt_Example

namespace StrategicPolicy.StochasticOpt

theorem nonstrategic_optimum :
    ∀ π ∈ Policies 3, IsMaxOn (uNS p0 q0 γ0) (Policies 3) π ↔ π = fun _ => 1 := by sorry

end StrategicPolicy.StochasticOpt
