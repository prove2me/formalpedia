-- Prove2me | Theorems.Thm_RevenueManagement_advance_purchase_beats_peak_load
-- name    : RevenueManagement.advance_purchase_beats_peak_load
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:09:40.000721+00:00
-- url     : https://prove2.me/theorems/a8a3517c-27a3-4810-bc1f-0a241738f931
-- title:
--   Sect. 8.3.6 (Gale and Holmes): the optimal advance-purchase discount ŵ exceeds the optimal peak-load discount w₂ and earns at least as much, V_APD(ŵ) ≥ V_peak(w₂)
-- statement:
--   In the two-flight monopoly of Sect. 8.3.6 with reservation price $v$, capacity $C$, peak
--   share $\alpha \in (0, 1)$ and waiting-cost distribution $F$ with density $f$, let
--   $w_2$ solve the peak-load first-order condition (8.13),
--   $(v - w)f(w) - F(w) = 1/\alpha - 1$, and $\hat w$ the advance-purchase condition (8.15),
--   $(v - w)f(w) - F(w) = 0$, with $f > 0$ and the marginal revenue $(v - w) - F(w)/f(w)$
--   strictly decreasing on $[0, w_C]$ (the book's uniqueness assumption: the page prints
--   "increasing", but its footnote 18 identifies it with the monotone marginal-revenue
--   Assumption 7.2, which in the waiting cost $w = v - u$ is decreasing), and let $\hat w$
--   maximize $V_{APD}$ on $[0, w_C]$. Then
--   $w_2 < \hat w$ and $V_{APD}(\hat w) \ge V_{peak}(w_2)$: advance-purchase discounts earn at
--   least the revenue of peak-load pricing.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 373-374, Sect. 8.3.6, Eq. (8.13)-(8.15), and Appendix 8.A p. 404 (proof that V_APD(ŵ) ≥ V_peak(w2))

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem advance_purchase_beats_peak_load (v C α wC : ℝ) (F f : ℝ → ℝ) (hα : 0 < α ∧ α < 1)
    (w2 wh : ℝ) (h2 : w2 ∈ Set.Icc 0 wC) (hw : wh ∈ Set.Icc 0 wC)
    (hf : ∀ w ∈ Set.Icc 0 wC, 0 < f w)
    (hψ : StrictAntiOn (fun w => (v - w) - F w / f w) (Set.Icc 0 wC))
    (h13 : (v - w2) * f w2 - F w2 = 1 / α - 1) (h15 : (v - wh) * f wh - F wh = 0)
    (hopt : ∀ w ∈ Set.Icc 0 wC, advancePurchaseRevenue v C α F w ≤ advancePurchaseRevenue v C α F wh) :
    w2 < wh ∧ peakLoadRevenue v C α F w2 ≤ advancePurchaseRevenue v C α F wh := by sorry

end RevenueManagement
