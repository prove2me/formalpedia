-- Prove2me | Theorems.Thm_PutermanMDP_MarkovPolicies_one_step_bounded
-- name    : PutermanMDP.MarkovPolicies.one_step_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:27.14769+00:00
-- url     : https://prove2.me/theorems/72dcec17-71bb-4f83-946c-e4ebe132431d
-- title:
--   Lemma 5.6.1 — one-step evaluation preserves bounded values
-- statement:
--   Let $S$ be a nonempty finite or countable state space. Suppose the real reward satisfies a uniform bound $|r(s,a)|\le M$ for all available actions. Let $0\le\beta\le1$, let $u$ be a bounded real function on $S$, and let $d$ be an admissible randomized Markov decision rule. With $r_d$ and $P_d$ its expected reward and transition operator,
--   $$r_d+\beta P_du\in V,$$
--   where $V$ is the space of bounded real functions on $S$.
--
--   This establishes that a single policy-evaluation step remains in the value-function space.
--
--   **Formalization Note** Membership in $V$ is expressed by existence of a uniform nonnegative real bound; no norm structure is assumed. The endpoint $\beta=1$ is included, as on the page.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 138 (PDF 154), Lemma 5.6.1

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_RewardCriteria

namespace PutermanMDP.MarkovPolicies

/-- Lemma 5.6.1: the randomized one-step operator maps V into V. -/
theorem one_step_bounded {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) (hM : RewardBounded M) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (u : S → ℝ) (hu : BoundedValue u)
    (d : (s : S) → PMF {a : A // a ∈ M.actions s}) :
    BoundedValue (oneStep M d β u) := by sorry

end PutermanMDP.MarkovPolicies
