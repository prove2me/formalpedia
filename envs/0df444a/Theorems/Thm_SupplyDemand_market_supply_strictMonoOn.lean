-- Prove2me | Theorems.Thm_SupplyDemand_market_supply_strictMonoOn
-- name    : SupplyDemand.market_supply_strictMonoOn
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:01.433779+00:00
-- url     : https://prove2.me/theorems/8547df93-62ea-4483-87a2-d449d2581bc9
-- title:
--   Market supply of upward-sloping firm supplies is upward-sloping
-- statement:
--   Let $s$ be a nonempty finite set of firms, and for each firm $i\in s$ let $f_i$ be its supply curve, strictly increasing on a set $I\subseteq\mathbb R$ of prices. Then the market supply curve, the horizontal sum
--   $$p\longmapsto\sum_{i\in s}f_i(p),$$
--   is strictly increasing on $I$.
--
--   The source defines the market supply curve as the sum of the quantities supplied by all suppliers at each price.
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Supply schedule" (market supply curve)

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem market_supply_strictMonoOn {ι : Type*} (I : Set ℝ) (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, StrictMonoOn (f i) I) :
    StrictMonoOn (marketCurve s f) I := by sorry

end SupplyDemand
