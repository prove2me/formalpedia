-- Prove2me | Theorems.Thm_StrategicQR_Game_corollary1_percentage
-- name    : StrategicQR.Game.corollary1_percentage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:26:15.762339+00:00
-- url     : https://prove2.me/theorems/5b416c29-5ccf-4536-b397-bbfa7ab8648b
-- title:
--   Corollary 1, p. 22 — under (6), the percentage gain from quick response is larger with strategic consumers: $\Delta/\pi^*\ge\Delta_m/\pi^m$
-- statement:
--   Under the hypotheses of Theorem 3 (MSLR, no rationing, $0<\alpha\le1$, $v_B<c_1<p$, $c_1\le c_2\le p$ and (6)), let $(q^*,v^*)$, $(q_r^*,v_r^*)$, $q^m$ and $q_r^m$ be as there. Then $\pi^*=\pi(q^*,v^*)>0$ and $\pi^m=\pi^m(q^m)>0$, and
--   $$\frac{\Delta}{\pi^*}=\frac{\pi_r^*-\pi^*}{\pi^*}\ \ge\ \frac{\pi_r^m-\pi^m}{\pi^m}=\frac{\Delta_m}{\pi^m}.$$
--
--   The relative increase in profit due to quick response is also larger when some consumers are strategic.
--
--   **Formalization Note** The positivity of $\pi^*$ and $\pi^m$ is part of the conclusion, so the quotients are genuine.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 22, Corollary 1

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Corollary 1 (p. 22). Under the hypotheses of Theorem 3 and for the same equilibria and
maximizers, the equilibrium profit `π*` and the myopic optimum `π^m` are positive, and the
percentage increase in profit due to quick response with strategic consumers,
`Δ/π* = (π*_r - π*)/π*`, is at least the one with only myopic consumers,
`Δ_m/π^m = (π_r^m - π^m)/π^m`. -/
theorem corollary1_percentage (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M)
    {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁) (hc₁p : c₁ < M.p)
    (hc₁₂ : c₁ ≤ c₂) (hc₂p : c₂ ≤ M.p)
    (h6 : (c₂ - c₁) / (c₂ - M.vB) ≤ (M.vM - M.p) / (M.vhi - M.vB))
    {q v qr vr qm qrm : ℝ}
    (heq : IsEquilibrium M α c₁ q v) (hqr : IsQREquilibrium M α c₁ c₂ qr vr)
    (hqm : qm ∈ Set.Ici (0 : ℝ))
    (hmax : IsMaxOn (fun q' => profit M 0 c₁ q' M.vhi) (Set.Ici 0) qm)
    (hqrm : qrm ∈ Set.Ici (0 : ℝ))
    (hrmax : IsMaxOn (fun q' => qrProfit M 0 c₁ c₂ q' M.vhi) (Set.Ici 0) qrm) :
    0 < profit M α c₁ q v ∧ 0 < profit M 0 c₁ qm M.vhi ∧
    (qrProfit M 0 c₁ c₂ qrm M.vhi - profit M 0 c₁ qm M.vhi) / profit M 0 c₁ qm M.vhi ≤
      (qrProfit M α c₁ c₂ qr vr - profit M α c₁ q v) / profit M α c₁ q v := by sorry

end StrategicQR.Game
