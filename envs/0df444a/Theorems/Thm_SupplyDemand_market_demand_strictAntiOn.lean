-- Prove2me | Theorems.Thm_SupplyDemand_market_demand_strictAntiOn
-- name    : SupplyDemand.market_demand_strictAntiOn
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:03.769022+00:00
-- url     : https://prove2.me/theorems/a6388b19-bb03-467c-85a8-05399694a2a6
-- title:
--   Market demand of downward-sloping individual demands is downward-sloping
-- statement:
--   Let $s$ be a nonempty finite set of buyers, and for each $i\in s$ let $f_i$ be the individual demand curve, strictly decreasing on a set $I\subseteq\mathbb R$ of prices. Then the market demand curve
--   $$p\longmapsto\sum_{i\in s}f_i(p)$$
--   is strictly decreasing on $I$.
--
--   The source defines the market demand curve by adding the quantities from the individual demand curves at each price. (This is the partial-equilibrium statement with fixed individual curves; the Sonnenschein–Mantel–Debreu discussion in the source concerns general equilibrium with income effects and is not contradicted.)
-- source:
--   Wikipedia, "Supply and demand", revision 1378800284, https://en.wikipedia.org/w/index.php?title=Supply_and_demand&oldid=1378800284, section "Demand schedule" (market demand curve)

import Mathlib
import Definitions.Def_SupplyDemand_Model

namespace SupplyDemand

theorem market_demand_strictAntiOn {ι : Type*} (I : Set ℝ) (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, StrictAntiOn (f i) I) :
    StrictAntiOn (marketCurve s f) I := by sorry

end SupplyDemand
