-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_remark3_iid
-- name    : RobustInventory.SingleStation.remark3_iid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:32:25.426432+00:00
-- url     : https://prove2.me/theorems/d4825110-d1ae-4afc-9f83-68caba944522
-- title:
--   §3.1, Remark 3 after Theorem 3.2, p. 156 — i.i.d. demand: $A_k = \hat w\Gamma_k$ and $w'_k = \bar w + \frac{p-h}{p+h}\hat w(\Gamma_k-\Gamma_{k-1})$
-- statement:
--   In the single-station model, suppose the demand is i.i.d. in the sense of the paper: $\bar w_k = \bar w$ and $\hat w_k = \hat w$ for all $k$, and suppose $\Gamma_0 \le 1$. Then for every $k$
--   $$A_k = \hat w\,\Gamma_k,\qquad w'_k = \bar w + \frac{p-h}{p+h}\,\hat w\,\big(\Gamma_k - \Gamma_{k-1}\big),$$
--   with $\Gamma_{-1} = 0$.
--
--   Combined with part (b) of Theorem 3.2, this gives the robust base-stock levels in closed form when there is no fixed cost.
--
--   **Formalization Note** $A_k = \hat w\Gamma_k$ needs $\Gamma_k \le k+1$ (otherwise $A_k = \hat w(k+1)$). The budget steps $\Gamma_{k+1} \le \Gamma_k + 1$ give this only if $\Gamma_0 \le 1$, which the page does not state; it is added as a hypothesis. The convention $\Gamma_{-1} = 0$ is the one consistent with $A_{-1} = 0$; it is stated as a separate clause for $k = 0$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 156 (PDF 7), §3.1, Remark 3 after Theorem 3.2

import Definitions.Def_RobustInventory_SingleStation_Deviation

namespace RobustInventory.SingleStation

/-- §3.1, Remark 3 after Theorem 3.2, p. 156: if the nominal demands and deviations are constant,
`w̄_k = w̄` and `ŵ_k = ŵ` for all `k`, and `Γ_0 ≤ 1`, then `A_k = ŵ Γ_k` for all `k`, and the
modified demand is `w'_k = w̄ + ((p - h)/(p + h)) ŵ (Γ_k - Γ_{k-1})`, with `Γ_{-1} = 0`. -/
theorem remark3_iid (M : Model) (wb wh : ℝ) (hwbar : ∀ k, M.wbar k = wb)
    (hwhat : ∀ k, M.what k = wh) (hΓ01 : M.Γ 0 ≤ 1) :
    (∀ k, M.A k = wh * M.Γ k) ∧
    M.wmod 0 = wb + (M.p - M.h) / (M.p + M.h) * wh * M.Γ 0 ∧
    (∀ k, M.wmod (k + 1) = wb + (M.p - M.h) / (M.p + M.h) * wh * (M.Γ (k + 1) - M.Γ k)) := by sorry

end RobustInventory.SingleStation
