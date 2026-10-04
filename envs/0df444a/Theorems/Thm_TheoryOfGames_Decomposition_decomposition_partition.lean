-- Prove2me | Theorems.Thm_TheoryOfGames_Decomposition_decomposition_partition
-- name    : TheoryOfGames.Decomposition.decomposition_partition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T04:32:34.341981+00:00
-- url     : https://prove2.me/theorems/a4cb9a36-70ec-414a-b954-982c60dffdff
-- title:
--   (43:F), (43:G), (43:H) — the minimal splitting sets partition I, and the splitting sets are exactly their unions
-- statement:
--   Let $I$ be a finite set of players and let $v$ be the characteristic function of a constant-sum game, i.e. $v$ satisfies (42:6:a)–(42:6:c):
--   $$v(\ominus) = 0, \qquad v(S) + v(-S) = v(I), \qquad v(S) + v(T) \leqq v(S \cup T) \text{ if } S \cap T = \ominus.$$
--   Call $J \subseteq I$ a splitting set if $v(S \cup T) = v(S) + v(T)$ for all $S \subseteq J$, $T \subseteq I - J$ (41:6), and a minimal splitting set if $J \neq \ominus$ is splitting and no proper subset $J' \neq \ominus$ of $J$ is splitting. Let $\Pi_\Gamma$ be the system of all minimal splitting sets. Then:
--
--   1. (43:F) any two different elements of $\Pi_\Gamma$ are disjunct;
--   2. (43:G) the sum of all elements of $\Pi_\Gamma$ is $I$: every player lies in some element of $\Pi_\Gamma$;
--   3. (43:H) by forming all sums of all possible aggregates of minimal splitting sets one obtains precisely the totality of all splitting sets: for every $K \subseteq I$,
--   $$K \text{ is a splitting set} \iff K = J_1 \cup \dots \cup J_p \text{ for some } J_1, \dots, J_p \in \Pi_\Gamma \ (p \geqq 0).$$
--
--   Thus $\Pi_\Gamma$ is a partition of $I$ (the *decomposition partition*), and it describes how far the decomposition of $\Gamma$ can be pushed without severing the ties which the rules of the game establish between players.
--
--   **Formalization Note** The player set is an arbitrary finite type `ι`; the statement also holds, trivially, when $I$ is empty, so the book's $n \geqq 1$ is not needed. An aggregate of minimal splitting sets is a `Finset (Finset ι)` $A$ of elements of $\Pi_\Gamma$, and its sum is `A.sup id`; the empty aggregate gives $\ominus$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 355, 43.3.2, (43:F), (43:G); p. 356, (43:H)

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

namespace TheoryOfGames.Decomposition

/-- (43:F), (43:G) and (43:H), 43.3.2: the minimal splitting sets of a constant-sum game are
pairwise disjunct, their sum is `I`, and by forming all sums of all possible aggregates of minimal
splitting sets we obtain precisely the totality of all splitting sets. -/
theorem decomposition_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    (∀ J₁ ∈ decompositionPartition v, ∀ J₂ ∈ decompositionPartition v,
        J₁ ≠ J₂ → Disjoint J₁ J₂) ∧
      (∀ k : ι, ∃ J ∈ decompositionPartition v, k ∈ J) ∧
      (∀ K : Finset ι, IsSplitting v K ↔
        ∃ A : Finset (Finset ι), (∀ J ∈ A, J ∈ decompositionPartition v) ∧
          K = A.sup id) := by sorry

end TheoryOfGames.Decomposition
