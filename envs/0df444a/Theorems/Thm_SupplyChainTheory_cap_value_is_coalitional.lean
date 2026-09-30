-- Prove2me | Theorems.Thm_SupplyChainTheory_cap_value_is_coalitional
-- name    : SupplyChainTheory.cap_value_is_coalitional
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:14:46.36318+00:00
-- url     : https://prove2.me/theorems/5dc73037-64cf-4bbf-9679-35167d29446b
-- title:
--   The combinatorial auction's value $V(T)$ is a coalitional value function: zero without the auctioneer and monotone in the coalition
-- statement:
--   For any valuations $v_{iS}$ of the bidders for the bundles of objects, the function
--   $V(T)$, the optimal value of the auctioneer's allocation problem restricted to the bidders of
--   $T$ (and $0$ when the auctioneer is not in $T$), is a coalitional value function: it vanishes on
--   coalitions without the auctioneer and is monotone, since an allocation among the bidders of $T$
--   is an allocation among those of any larger coalition. These are the two properties of $V$ that
--   Lemma 15.1 and Theorems 15.2 and 15.3 use.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 605-606, Sect. 15.4.3, the definition of the coalitional value function V(T) ('In other words, V(T) is the optimal objective function value of the auctioneer's problem in the VCG auction, with N replaced by T \ 0')

import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem cap_value_is_coalitional {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) :
    IsCoalitionalValue (capValue v) := by sorry

end SupplyChainTheory
