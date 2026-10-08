-- Prove2me | Theorems.Thm_StrategicQR_Game_theorem2_all_buy_early
-- name    : StrategicQR.Game.theorem2_all_buy_early
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:26:07.806739+00:00
-- url     : https://prove2.me/theorems/7c21df11-3850-4078-bfeb-7babcf97a972
-- title:
--   Theorem 2 (iii), p. 20 — under (6), in equilibrium with quick response all strategic consumers buy in the first period
-- statement:
--   Assume MSLR and no rationing, $0<\alpha\le1$, $v_B<c_1\le c_2\le p$, and condition (6):
--   $$\frac{v_M-p}{\bar v-v_B}\ge\frac{c_2-c_1}{c_2-v_B}.$$
--   Then every rational expectations equilibrium $(q_r^*,v_r^*)$ with quick response has $v_r^*=\bar v$ — all strategic consumers purchase in the first period — and $q_r^*$ maximizes the myopic profit with quick response $\pi_r^m$ on $[0,\infty)$, i.e. $q_r^*=q_r^m$.
--
--   Quick response lets the retailer keep its initial stock low enough that a deep discount is unlikely, which removes strategic waiting altogether.
--
--   **Formalization Note** The theorem says "in equilibrium"; the statement is for every equilibrium, which is the reading Theorem 3's proof needs ($\pi_r^*=\pi_r^m$). The second conclusion is the step "the equilibrium stocking level must be the myopic optimal with quick response, $q_r^m$" of the proof.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 20, Theorem 2, condition (6) and last sentence; p. 21, proof part (iii)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Theorem 2, last sentence (p. 20; proof part (iii), p. 21). Under MSLR and no rationing, for
`0 < α ≤ 1`, `vB < c₁ ≤ c₂ ≤ p` and condition (6), `(vM - p)/(v̄ - vB) ≥ (c₂ - c₁)/(c₂ - vB)`,
every rational expectations equilibrium `(q*_r, v*_r)` with quick response has `v*_r = v̄` (all
strategic consumers buy in the first period), and `q*_r` maximizes the myopic profit with quick
response `π_r^m` on `[0, ∞)`. -/
theorem theorem2_all_buy_early (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M)
    {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hc₂p : c₂ ≤ M.p) (h6 : (c₂ - c₁) / (c₂ - M.vB) ≤ (M.vM - M.p) / (M.vhi - M.vB))
    {q v : ℝ} (heq : IsQREquilibrium M α c₁ c₂ q v) :
    v = M.vhi ∧ IsMaxOn (fun q' => qrProfit M 0 c₁ c₂ q' M.vhi) (Set.Ici 0) q := by sorry

end StrategicQR.Game
