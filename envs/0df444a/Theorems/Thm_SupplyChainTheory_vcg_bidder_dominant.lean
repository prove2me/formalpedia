-- Prove2me | Theorems.Thm_SupplyChainTheory_vcg_bidder_dominant
-- name    : SupplyChainTheory.vcg_bidder_dominant
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:17:38.676623+00:00
-- url     : https://prove2.me/theorems/3bf03218-12c3-48d1-8bb9-762f7c2a65d5
-- title:
--   Theorem 15.2: the VCG vector is the bidder-dominant core point when it lies in the core, and otherwise no bidder-dominant point exists and the auctioneer's VCG payoff is below every core payoff
-- statement:
--   **Theorem 15.2.** If the VCG payoff vector $\bar\pi$ lies in the core, then it is the
--   bidder-dominant point; otherwise, there is no bidder-dominant point in the core, and the
--   auctioneer's VCG payoff is strictly less than the smallest of the auctioneer's core payoffs,
--   $\bar\pi_0 < \hat\pi_0$ for every $\hat\pi \in C(L, V)$.
--
--   The first part is Lemma 15.1. For the second, any core vector $\hat\pi$ pays every bidder at
--   most its VCG payoff and some bidder strictly less, so it pays the auctioneer strictly more than
--   $\bar\pi_0$; and the core vector of Lemma 15.1 for that bidder shows $\hat\pi$ is not bidder
--   dominant. The theorem says the VCG auction's revenue falls below every competitive outcome
--   unless its payoff vector is in the core.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 607, Sect. 15.4.3, Theorem 15.2 and its proof

import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem vcg_bidder_dominant {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (hV : IsCoalitionalValue V) :
    (InCore V Finset.univ (vcgPayoff V Finset.univ) → BidderDominant V Finset.univ (vcgPayoff V Finset.univ))
      ∧ (¬ InCore V Finset.univ (vcgPayoff V Finset.univ) →
          (¬ ∃ π, BidderDominant V Finset.univ π)
          ∧ ∀ π, InCore V Finset.univ π → vcgPayoff V Finset.univ 0 < π 0) := by sorry

end SupplyChainTheory
