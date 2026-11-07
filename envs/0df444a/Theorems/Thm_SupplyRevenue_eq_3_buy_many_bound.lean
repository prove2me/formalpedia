-- Prove2me | Theorems.Thm_SupplyRevenue_eq_3_buy_many_bound
-- name    : SupplyRevenue.eq_3_buy_many_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:32.982711+00:00
-- url     : https://prove2.me/theorems/8a2c950e-b389-4af7-9439-f1abe2cba0b6
-- title:
--   Display (3) — $B(D)\le 4K A_{1/(2K)}(D)$
-- statement:
--   For every independent finite monotone instance on $n,m\ge 1$,
--
--   $$B(D)\le 4K\,A_{1/(2K)}(D).$$
--
--   Combined with the $A_{1/(2K)}$ column it yields the $B$ column of the goal.
--
--   Differences from the source:
--   - reading: "a fixed residual bundle order" → any injective rank `tie : Finset (Fin m) ↪ ℕ`, one per statement; reason: R3: the order is unspecified on the page, so every statement holds for every rank
--   - reading: "adaptive closures and limits" of buy-many menus → a menu is any set of options containing the empty option, dominating every finite-depth adaptive strategy, with no closedness imposed; reason: R5: finite-depth strategies suffice for the p.6 step, and a menu dominated only in the limit has a closure in this class
--   - reading: the option chosen from a menu → any utility-maximizing option on supported types, with no payment tie; reason: R6: this makes $B$ larger, hence the upper bound stronger, and the values of §9 are unchanged
--   - reading: capped single-buyer revenue $R_{BM}(D_i,x_i)$ → supremum over finite mixtures of certificates with expected inclusion marginals at most $x_i$; $x\ge 0$ in (1); reason: R7: p.2 "Sources may mix menus independently of type"
--   - encoding: suprema and ratios of revenues → suprema in $\mathbb R_{\ge0}\cup\{\infty\}$, constants as `ENNReal.ofReal`; reason: R9: same values; the inequalities hold literally at zero, with no junk value
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §2, p.6, (3)

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev
import Definitions.Def_SupplyRevenue_BuyMany

open scoped ENNReal

namespace SupplyRevenue

/-- Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
display (3), p.6: `B(D) ≤ 4K A_{1/(2K)}(D)` for finite monotone types.

**Formalization Note** `1/(2K)` is real division; `K = capK m ≥ 2`. -/
theorem eq_3_buy_many_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (tie : Tie m) (D : Instance n m) :
    buyManyRev D ≤
      ENNReal.ofReal (4 * (capK m : ℝ)) * capRev tie D (1 / (2 * (capK m : ℝ))) := by sorry

end SupplyRevenue
