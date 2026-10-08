-- Prove2me | Theorems.Thm_StrategicQR_Game_theorem2_existence
-- name    : StrategicQR.Game.theorem2_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:59.715149+00:00
-- url     : https://prove2.me/theorems/958c8e92-75c8-4269-97ba-2b7d6eb8b364
-- title:
--   Theorem 2 (i), p. 20 — an RE equilibrium $(q_r^*,v_r^*)$ with quick response exists
-- statement:
--   Assume MSLR and no rationing. For $0<\alpha\le1$ and $v_B<c_1\le c_2\le p$, there exists a rational expectations equilibrium $(q_r^*,v_r^*)$ of the game between the retailer with quick response and the strategic consumers: $q_r^*\ge0$ maximizes $\pi_r(\cdot,v_r^*)$ on $[0,\infty)$ and $v_r^*$ is a consumer best response to $q_r^*$.
--
--   The consumer best response is the same with and without quick response (p. 19), so only the retailer's side changes.
--
--   **Formalization Note** The paper says "the proof is identical to Theorem 1"; the same remark about the best-response correspondence applies. The comparison "$q_r^*\le q^*$ and $\pi_r^*\ge\pi^*$" of Theorem 2 is not part of this statement (see the mission description).
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 20, Theorem 2; proof part (i)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Theorem 2, existence part (p. 20; "the proof is identical to Theorem 1"). Under MSLR and no
rationing, for `0 < α ≤ 1` and `vB < c₁ ≤ c₂ ≤ p`, a rational expectations equilibrium
`(q*_r, v*_r)` of the game with quick response exists. -/
theorem theorem2_existence (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M)
    {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hc₂p : c₂ ≤ M.p) :
    ∃ q v, IsQREquilibrium M α c₁ c₂ q v := by sorry

end StrategicQR.Game
