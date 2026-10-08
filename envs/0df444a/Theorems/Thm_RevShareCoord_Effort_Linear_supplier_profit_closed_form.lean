-- Prove2me | Theorems.Thm_RevShareCoord_Effort_Linear_supplier_profit_closed_form
-- name    : RevShareCoord.Effort.Linear.supplier_profit_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:05:54.166784+00:00
-- url     : https://prove2.me/theorems/59c45cb7-16c4-48ea-aad2-75ad60f46353
-- title:
--   Sec. 4.2.2, p. 24 — π_s(w(φ), φ) = (1 − c)²/(4(1 + φ(1 − 2τ²)))
-- statement:
--   In the linear example, let $0 \le \tau < 1$, $0 < c < 1$ and $0 < \phi \le 1$. At the wholesale price $w(\phi) = \phi\big((1-\tau^2)\phi + c(1-\phi\tau^2)\big)/\big(1 + \phi(1-2\tau^2)\big)$, with the retailer ordering $q(w(\phi), \phi)$ and exerting effort $e = \phi\tau q$, the supplier's profit simplifies to
--
--   $$
--   \pi_s(w(\phi), \phi) = \frac{(1 - c)^2}{4\big(1 + \phi(1 - 2\tau^2)\big)} .
--   $$
--
--   This closed form is what the comparison of revenue-sharing and wholesale-price contracts rests on.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 24 (PDF p. 25), Section 4.2.2, 'The supplier profit function simplifies to π_s(w(φ), φ) = (1 − c)²/(4(1 + φ(1 − 2τ²)))'

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, p. 24: at the wholesale price `w(φ)` the supplier's profit simplifies to
`π_s(w(φ), φ) = (1 − c)²/(4(1 + φ(1 − 2τ²)))`. -/
theorem supplier_profit_closed_form (τ c φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    supplierProfitAt τ c φ (wholesalePrice τ c φ) =
      (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) := by sorry

end RevShareCoord.Effort.Linear
