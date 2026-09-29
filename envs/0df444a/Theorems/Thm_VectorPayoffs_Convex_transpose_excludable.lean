-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_transpose_excludable
-- name    : VectorPayoffs.Convex.transpose_excludable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:09:30.999369+00:00
-- url     : https://prove2.me/theorems/d6856d80-9bfd-4131-9817-2a8166878353
-- title:
--   §1, p. 2 — a closed set disjoint from a set approachable in M′ is excludable in M with the same strategy
-- statement:
--   Let $S,T\subseteq\mathbb R^N$ be closed and disjoint, and let $f$ be a strategy (with $s$ pure actions) with which $S$ is approachable in the transpose $M'$. Then $T$ is excludable in $M$ with the strategy $f$ for Player II.
--
--   This is the paper's "obvious fact" that converts any sufficient condition for approachability into a sufficient condition for excludability; with THEOREM 1 it gives the excludability clause of THEOREM 3.
--
--   **Formalization Note** Neither $S$ nor $T$ is assumed bounded; the boundedness of $X$ (which contains every average payoff almost surely) is what keeps the two sets apart where it matters.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 2, §1, second sentence of the paragraph after the N = 1 analog

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §1, p. 2: if a closed set `S` is approachable in the transpose `M'` with a
strategy `f`, then every closed set `T` not intersecting `S` is excludable in `M` with `f`. -/
theorem transpose_excludable {N r s : ℕ} (G : Game N r s) (S T : Set (E N))
    (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T) (f : Strategy N s)
    (hf : G.transpose.ApproachableWith S f) : G.ExcludableWith T f := by sorry

end VectorPayoffs.Convex
