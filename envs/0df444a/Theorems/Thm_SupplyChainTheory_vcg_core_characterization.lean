-- Prove2me | Theorems.Thm_SupplyChainTheory_vcg_core_characterization
-- name    : SupplyChainTheory.vcg_core_characterization
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:19:15.378993+00:00
-- url     : https://prove2.me/theorems/45055b98-aae9-4b8e-a49c-f9d318dfe5f9
-- title:
--   Theorem 15.3: $V$ is bidder-submodular iff the core of every coalition is $\Pi_S$ iff the VCG vector of every coalition lies in its core
-- statement:
--   **Theorem 15.3.** For a coalitional value function $V$, the following three statements are
--   equivalent:
--
--   (i) $V$ is bidder-submodular: for every bidder $k$ and coalitions $0 \in S \subseteq S'$,
--   $V(S \cup k) - V(S) \ge V(S' \cup k) - V(S')$;
--
--   (ii) for every coalition $S \ni 0$, $C(S, V) = \Pi_S$, where
--   $\Pi_S = \{\pi : \sum_{k \in S}\pi_k = V(S),\ 0 \le \pi_k \le \bar\pi_k(S)\ \forall k \in S \setminus 0\}$;
--
--   (iii) for every coalition $S \ni 0$, the VCG payoff vector $\bar\pi(S)$ lies in $C(S, V)$.
--
--   Bidder-submodularity is thus exactly the condition under which the VCG auction's payoff vector
--   is a competitive outcome whatever the set of participating bidders, so that the revenue
--   deficiency, non-monotonicity, collusion and false-name defects of Sect. 15.4.2 cannot occur.
--   The book's proof shows (i) $\Rightarrow$ (ii) by telescoping the marginal contributions along
--   a chain of coalitions, (ii) $\Rightarrow$ (iii) since $\bar\pi(S) \in \Pi_S$, and (iii)
--   $\Rightarrow$ (i) by exhibiting, from a failure of submodularity, a coalition that blocks its
--   own VCG vector.
--
--   **Formalization Note** The statement is the conjunction (i) $\Leftrightarrow$ (ii) and (i)
--   $\Leftrightarrow$ (iii); payoff vectors are functions on all players, and the conditions
--   defining the core and $\Pi_S$ involve only the players of $S$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 607-608, Sect. 15.4.3, Theorem 15.3 and its proof; after Ausubel and Milgrom (2006)

import Definitions.Def_SupplyChainTheory_auctions

namespace SupplyChainTheory

theorem vcg_core_characterization {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ)
    (hV : IsCoalitionalValue V) :
    (BidderSubmodular V ↔ ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → ∀ π,
        InCore V S π ↔ (∑ k ∈ S, π k = V S ∧ ∀ k ∈ S, k ≠ 0 → 0 ≤ π k ∧ π k ≤ vcgPayoff V S k))
      ∧ (BidderSubmodular V ↔ ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S →
          InCore V S (vcgPayoff V S)) := by sorry

end SupplyChainTheory
