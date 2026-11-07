-- Prove2me | Theorems.Thm_SupplyRevenue_doubled_cost_transfer
-- name    : SupplyRevenue.doubled_cost_transfer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:11.262541+00:00
-- url     : https://prove2.me/theorems/b2cfcc24-cfb6-463f-97e5-a8b3000a92ce
-- title:
--   Whole-outcome doubled-cost transfer — BM Profit$_{2c}$ ≤ $2\ln(4m)$ IP Profit$_c$ ≤ $2K$ IP Profit$_c$
-- statement:
--   Let $b$ be a finite monotone buyer on $m\ge 1$ items and $c\ge 0$ a cost vector. Then
--
--   $$\mathrm{BM\ Profit}_{2c}(b)\le 2\ln(4m)\,\mathrm{IP\ Profit}_c(b)\le 2K\,\mathrm{IP\ Profit}_c(b).$$
--
--   Valuation is the expected value of the whole lottery, and costs alone use inclusion marginals. This step transfers buy-many revenue to item pricing with logarithmic loss, which is where the factor $K$ of the $B$ column comes from.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: "adaptive closures and limits" of buy-many menus → a menu is any set of options containing the empty option, dominating every finite-depth adaptive strategy, with no closedness imposed; reason: R5: finite-depth strategies suffice for the p.6 step, and a menu dominated only in the limit has a closure in this class
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
--   - reading: "BM Profit" over menus → supremum over single certificates; reason: p.2: "Unconstrained single-buyer profit under random menus cannot exceed the deterministic-menu supremum"
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §2, p.6, "Whole-outcome doubled-cost transfer"

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_BuyMany
import Definitions.Def_SupplyRevenue_Local

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§2, p.6, "Whole-outcome doubled-cost transfer": `BM Profit_{2c}(D_i) ≤ 2 ln(4m) IP Profit_c(D_i) ≤ 2K IP Profit_c(D_i)`.

**Formalization Note** Valuation is the expected value of the whole lottery, and costs use inclusion marginals alone.
`c` is the cost vector, not the goal's constant. Certificates select any utility-maximizing option (reading R6), which is
what p.6's "the original chosen lottery" needs. Both profits are suprema in `ℝ≥0∞`. -/
theorem doubled_cost_transfer {m : ℕ} (hm : 0 < m) (tie : Tie m) (b : Buyer m) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) :
    bmProfit b (fun j => 2 * c j) ≤ ENNReal.ofReal (2 * Real.log (4 * (m : ℝ))) * ipProfit tie b c ∧
    ENNReal.ofReal (2 * Real.log (4 * (m : ℝ))) * ipProfit tie b c ≤
      ENNReal.ofReal (2 * (capK m : ℝ)) * ipProfit tie b c := by sorry

end SupplyRevenue
