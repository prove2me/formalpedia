-- Prove2me | Theorems.Thm_PutermanMDP_MarkovPolicies_geometric_discount
-- name    : PutermanMDP.MarkovPolicies.geometric_discount
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:16.383282+00:00
-- url     : https://prove2.me/theorems/78c1419c-9068-4a14-b044-2142b4f2e458
-- title:
--   Proposition 5.3.1 — geometric horizon equals discounting
-- statement:
--   Consider a stationary model on a nonempty finite or countable state space, with uniformly bounded rewards on available actions. Let $\pi$ be any admissible randomized history-dependent policy. For $0\le\beta<1$, let the independent horizon $\nu$ satisfy $\Pr(\nu=n)=(1-\beta)\beta^{n-1}$ for $n\ge1$. For every starting state $s$,
--   $$v_\nu^\pi(s)=v_\beta^\pi(s).$$
--
--   Thus geometric termination and discounting give the same expected reward for each fixed policy.
--
--   **Formalization Note** The random-horizon expectation is the mixture of the fixed-horizon expected returns, with zero terminal reward. This encodes the independence convention directly. The endpoint $\beta=0$ gives one reward period, not zero periods.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 126 (PDF 142), Proposition 5.3.1; independence and geometric convention on pp. 125–126

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_RewardCriteria

namespace PutermanMDP.MarkovPolicies

/-- Proposition 5.3.1, including β=0 and a horizon supported on 1,2,... . -/
theorem geometric_discount {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) (hM : RewardBounded M) (π : HistoryPolicy M)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ s : S, geometricReturn M π (PMF.pure s) β =
      discountedReturn M π (PMF.pure s) β := by sorry

end PutermanMDP.MarkovPolicies
