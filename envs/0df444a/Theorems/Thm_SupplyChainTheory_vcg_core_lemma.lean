-- Prove2me | Theorems.Thm_SupplyChainTheory_vcg_core_lemma
-- name    : SupplyChainTheory.vcg_core_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:15:50.864431+00:00
-- url     : https://prove2.me/theorems/55511261-98a0-4981-8260-a6e4aaa1dd16
-- title:
--   Lemma 15.1: the core is nonempty and each bidder's VCG payoff is the largest payoff it receives at any core point
-- statement:
--   **Lemma 15.1.** For a coalitional value function $V$ on the players $L = \{0\} \cup N$, the core
--   $C(L, V)$ is nonempty, and for every bidder $k$,
--
--   $$ \bar\pi_k \;=\; \max\{\pi_k : \pi \in C(L, V)\}, $$
--
--   the VCG payoff $\bar\pi_k = V(L) - V(L \setminus k)$ is the greatest payoff bidder $k$ receives at
--   any point of the core. The book's proof: the vector paying $V(L \setminus k)$ to the auctioneer,
--   $V(L) - V(L \setminus k)$ to $k$ and nothing to the other bidders lies in the core, and any core
--   vector paying $k$ more would pay the coalition $L \setminus k$ less than $V(L \setminus k)$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 606, Sect. 15.4.3, Lemma 15.1 and its proof

import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem vcg_core_lemma {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (hV : IsCoalitionalValue V) :
    (∃ π, InCore V Finset.univ π)
      ∧ ∀ k : Fin (n + 1), k ≠ 0 →
        IsGreatest {x | ∃ π, InCore V Finset.univ π ∧ x = π k} (vcgPayoff V Finset.univ k) := by sorry

end SupplyChainTheory
