-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_not_approachable_and_excludable
-- name    : VectorPayoffs.Convex.not_approachable_and_excludable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:08:55.790614+00:00
-- url     : https://prove2.me/theorems/dd5f53ad-aaba-44cb-bc10-740f4a6fda96
-- title:
--   §1, p. 2 — no set is both approachable and excludable
-- statement:
--   Let $M$ be an $r\times s$ vector-payoff game with $r,s\ge1$. No set $S\subseteq\mathbb R^N$ is both approachable and excludable in $M$:
--   $$\neg\big(S\text{ approachable in }M\ \wedge\ S\text{ excludable in }M\big).$$
--
--   This is the last clause of the paper's remark "Obviously any superset of an approachable set is approachable, any subset of an excludable set is excludable, and no set is both approachable and excludable." It is what turns excludability into non-approachability in THEOREM 3.
--
--   **Formalization Note** The statement is not a formality: approachability and excludability quantify over plays, so the clause needs a play of any pair of strategies to exist (the Ionescu–Tulcea construction). $r,s\ge1$ is added so that both players have strategies.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 2, §1, paragraph after the N = 1 analog, first sentence (last clause)

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §1, p. 2: no set is both approachable and excludable. -/
theorem not_approachable_and_excludable {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r)
    (hs : 1 ≤ s) (S : Set (E N)) : ¬ (G.ApproachableIn S ∧ G.ExcludableIn S) := by sorry

end VectorPayoffs.Convex
