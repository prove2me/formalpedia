-- Prove2me | Theorems.Thm_PutermanMDP_MarkovPolicies_initial_distribution
-- name    : PutermanMDP.MarkovPolicies.initial_distribution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:28.011103+00:00
-- url     : https://prove2.me/theorems/678d2875-9097-468a-bcb5-119602e023ba
-- title:
--   Corollary 5.5.2 — Markovization for an initial distribution
-- statement:
--   Let $\mu$ be any initial-state distribution on a nonempty finite or countable state space, and let $\pi$ be any admissible randomized history-dependent policy. There exists one randomized Markov policy $\pi'$ such that, for every epoch $t\ge1$, state $j$, and available action $a$,
--   $$\Pr_\mu^{\pi'}(X_t=j,Y_t=a)=\Pr_\mu^\pi(X_t=j,Y_t=a).$$
--
--   The replacement may depend on $\mu$ and $\pi$, but the same replacement works at all epochs. The result extends marginal preservation from a fixed starting state to a given initial distribution.
--
--   **Formalization Note** Lean uses zero-based time $n=t-1$. The statement compares one-time marginals and does not assert equality of whole path laws.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 135 (PDF 151), Corollary 5.5.2

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_Model

namespace PutermanMDP.MarkovPolicies

/-- Corollary 5.5.2: the Markov replacement may depend on the initial law. -/
theorem initial_distribution {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) :
    ∀ μ : PMF S, ∀ π : HistoryPolicy M, ∃ π' : MarkovPolicy M,
      ∀ (n : ℕ) (j : S) (a : A), a ∈ M.actions j →
        stateActionLaw M π'.toHistory μ n (j, a) =
          stateActionLaw M π μ n (j, a) := by sorry

end PutermanMDP.MarkovPolicies
