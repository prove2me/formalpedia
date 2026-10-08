-- Prove2me | Theorems.Thm_StrategicQR_Game_theorem1_existence
-- name    : StrategicQR.Game.theorem1_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:17.956437+00:00
-- url     : https://prove2.me/theorems/127c901b-1cf9-433f-9c7e-ee4c096ed43d
-- title:
--   Theorem 1 (i), p. 16 — a rational expectations equilibrium $(q^*,v^*)$ exists
-- statement:
--   Assume the demand density has the MSLR property and the no-rationing condition holds. For $0<\alpha\le1$ and unit cost $v_B<c<p$, there exists a rational expectations equilibrium $(q^*,v^*)$: $q^*\ge0$ maximizes $\pi(\cdot,v^*)$ on $[0,\infty)$, and $v^*$ is a consumer best response to $q^*$.
--
--   Existence is the foundation of every equilibrium comparison in the paper.
--
--   **Formalization Note** The printed proof treats the best response $v^*(q)$ as a continuous function and applies the intermediate value theorem to the first-order condition. $v^*(q)$ is a correspondence (p. 11), so a complete proof needs more care; the statement is unchanged. No rationing is the corrected form of the paper's standing assumption $\theta_c\le\theta$ (p. 15). $c<p$ is the reading of the proof's "$p-c>0$".
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 16, Theorem 1; pp. 16–17, proof part (i)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Theorem 1, existence part (p. 16; proof part (i), pp. 16–17). Under MSLR and the no-rationing
assumption, for `0 < α ≤ 1` and `vB < c < p`, a rational expectations equilibrium `(q*, v*)`
exists. -/
theorem theorem1_existence (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M) {α c : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : M.vB < c) (hcp : c < M.p) :
    ∃ q v, IsEquilibrium M α c q v := by sorry

end StrategicQR.Game
