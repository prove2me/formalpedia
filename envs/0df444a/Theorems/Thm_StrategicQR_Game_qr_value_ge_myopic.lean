-- Prove2me | Theorems.Thm_StrategicQR_Game_qr_value_ge_myopic
-- name    : StrategicQR.Game.qr_value_ge_myopic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:54.075997+00:00
-- url     : https://prove2.me/theorems/3e186619-86ae-499a-9e95-202de39b1962
-- title:
--   Theorem 3, p. 21 — under (6), quick response is more valuable with strategic consumers: $\pi_r^*-\pi^*\ge\pi_r^m-\pi^m$
-- statement:
--   Assume the demand density has the MSLR property and the no-rationing condition holds. Let some consumers be strategic, $0<\alpha\le1$, let the unit costs satisfy $v_B<c_1<p$ and $c_1\le c_2\le p$, and let condition (6) hold:
--   $$\frac{v_M-p}{\bar v-v_B}\ge\frac{c_2-c_1}{c_2-v_B}.$$
--   Let $(q^*,v^*)$ be any rational expectations equilibrium without quick response (unit cost $c_1$), $(q_r^*,v_r^*)$ any equilibrium with quick response, $q^m\ge0$ any maximizer of the myopic profit $\pi^m$ and $q_r^m\ge0$ any maximizer of the myopic profit with quick response $\pi_r^m$. Then the value of quick response with strategic consumers is at least its value with only myopic consumers:
--   $$\Delta=\pi_r(q_r^*,v_r^*)-\pi(q^*,v^*)\ \ge\ \pi_r^m(q_r^m)-\pi^m(q^m)=\Delta_m .$$
--
--   With myopic consumers quick response only matches supply with exogenous demand; with strategic consumers it also influences demand, by making deep discounts unlikely and pushing strategic consumers to buy at full price.
--
--   **Formalization Note**
--   - **Same retailer.** The retailer without quick response has unit cost $c_1$, so $\Delta$ compares the same retailer with and without the second order (p. 20: no quick response is quick response with $c_2=p$).
--   - **Myopic benchmarks.** These are the same profit functions at $\alpha=0$ (belief irrelevant, evaluated at $\bar v$).
--   - **Added hypotheses.** $v_B>0$, $p<v_M$ and the finite mean are added in the model. $c_1<p$ is the reading of the "$p-c>0$" step in the proof of Theorem 1, which this proof uses.
--   - **No rationing** is the paper's standing assumption $\theta_c\le\theta$, in corrected form; it is included as such.
--   - **Every equilibrium.** The statement quantifies over every equilibrium and every maximizer, which is the faithful reading of "the value of quick response".
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 21, Theorem 3 and its proof; p. 20, condition (6)

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Theorem 3 (p. 21). Under MSLR and no rationing, let some consumers be strategic
(`0 < α ≤ 1`), let `vB < c₁ < p`, `c₁ ≤ c₂ ≤ p`, and let (6) hold:
`(vM - p)/(v̄ - vB) ≥ (c₂ - c₁)/(c₂ - vB)`. For every equilibrium `(q*, v*)` without quick
response (unit cost `c₁`), every equilibrium `(q*_r, v*_r)` with quick response, every maximizer
`q^m` of the myopic profit `π^m` and every maximizer `q_r^m` of the myopic profit with quick
response `π_r^m`, the value of quick response `Δ = π*_r - π*` is at least its myopic value
`Δ_m = π_r^m - π^m`. -/
theorem qr_value_ge_myopic (M : Model) (hmslr : MSLR M.f) (hNR : NoRationing M)
    {α c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc₁ : M.vB < c₁) (hc₁p : c₁ < M.p)
    (hc₁₂ : c₁ ≤ c₂) (hc₂p : c₂ ≤ M.p)
    (h6 : (c₂ - c₁) / (c₂ - M.vB) ≤ (M.vM - M.p) / (M.vhi - M.vB))
    {q v qr vr qm qrm : ℝ}
    (heq : IsEquilibrium M α c₁ q v) (hqr : IsQREquilibrium M α c₁ c₂ qr vr)
    (hqm : qm ∈ Set.Ici (0 : ℝ))
    (hmax : IsMaxOn (fun q' => profit M 0 c₁ q' M.vhi) (Set.Ici 0) qm)
    (hqrm : qrm ∈ Set.Ici (0 : ℝ))
    (hrmax : IsMaxOn (fun q' => qrProfit M 0 c₁ c₂ q' M.vhi) (Set.Ici 0) qrm) :
    qrProfit M 0 c₁ c₂ qrm M.vhi - profit M 0 c₁ qm M.vhi ≤
      qrProfit M α c₁ c₂ qr vr - profit M α c₁ q v := by sorry

end StrategicQR.Game
