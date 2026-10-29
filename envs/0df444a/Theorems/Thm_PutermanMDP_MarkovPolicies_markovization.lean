-- Prove2me | Theorems.Thm_PutermanMDP_MarkovPolicies_markovization
-- name    : PutermanMDP.MarkovPolicies.markovization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:30:24.99108+00:00
-- url     : https://prove2.me/theorems/e998eccf-3413-4171-92bc-0748044f73f3
-- title:
--   Theorem 5.5.1 — Markovization preserves state-action marginals
-- statement:
--   Let $\pi$ be an admissible randomized history-dependent policy in a stationary model on a nonempty finite or countable state space. For each initial state $s$, there exists a randomized Markov policy $\pi'$ such that, for every epoch $t\ge1$, state $j$, and action $a\in A_j$,
--   $$\Pr^{\pi'}(X_t=j,Y_t=a\mid X_1=s)
--    =\Pr^\pi(X_t=j,Y_t=a\mid X_1=s).$$
--
--   One replacement policy preserves all the time marginals simultaneously. It may depend on the specified initial state. This is the distributional foundation for comparing expected reward criteria under history-dependent and Markov policies.
--
--   **Formalization Note** Lean starts the process from the point mass at $s$, which represents the conditional notation on the page without conditioning an arbitrary initial law on a null event. Time $n=0$ represents epoch $1$. No boundedness or integrability of rewards is assumed, because the conclusion concerns only probability distributions. The replacement need not be deterministic or stationary.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 134 (PDF 150), Theorem 5.5.1, Eq. (5.5.1)

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_Model

namespace PutermanMDP.MarkovPolicies

/-- Theorem 5.5.1: one Markov replacement matches every time marginal. -/
theorem markovization {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) (π : HistoryPolicy M) :
    ∀ s : S, ∃ π' : MarkovPolicy M, ∀ (n : ℕ) (j : S) (a : A),
      a ∈ M.actions j →
      stateActionLaw M π'.toHistory (PMF.pure s) n (j, a) =
        stateActionLaw M π (PMF.pure s) n (j, a) := by sorry

end PutermanMDP.MarkovPolicies
