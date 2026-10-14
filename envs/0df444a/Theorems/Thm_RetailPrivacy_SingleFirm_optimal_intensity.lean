-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_optimal_intensity
-- name    : RetailPrivacy.SingleFirm.optimal_intensity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:32.644012+00:00
-- url     : https://prove2.me/theorems/3d581e6e-b2d6-4f50-8302-efa9a6cbf94e
-- title:
--   §4.1, p. 11 — the optimal monetization intensity r(s) = δs/(2c), increasing in s
-- statement:
--   Let $c > 0$, $\delta \in (0,1)$, and let $s \ge 0$ be the number of consumers who disclose data. The firm's downside exploitation profit at intensity $r \ge 0$ is $r\delta s - c r^2$. Then
--   $$r(s) = \frac{\delta s}{2c}$$
--   maximizes $r\delta s - c r^2$ over $r \ge 0$, it is the only maximizer, and it is strictly increasing in $s$.
--
--   This is the last stage of the $\mathbb R$-mode game: the firm's exploitation intensity as a function of the realized disclosing quantity, which enters the rational-expectations condition.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 11, §4.1, last paragraph

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem optimal_intensity (c δ s : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hs : 0 ≤ s) :
    IsMaxOn (fun r => dataProfit c δ s r) (Set.Ici 0) (δ * s / (2 * c)) ∧
    (∀ r ∈ Set.Ici (0 : ℝ), IsMaxOn (fun r' => dataProfit c δ s r') (Set.Ici 0) r →
      r = δ * s / (2 * c)) ∧
    StrictMono (fun s' : ℝ => δ * s' / (2 * c)) := by sorry

end RetailPrivacy.SingleFirm
