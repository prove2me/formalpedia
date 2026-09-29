-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_convex_approachable_iff
-- name    : VectorPayoffs.Convex.convex_approachable_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:11:02.303806+00:00
-- url     : https://prove2.me/theorems/c10437d6-2b7f-41d6-9569-086e16817bfa
-- title:
--   THEOREM 3 — a closed convex set is approachable iff it meets every T(q); otherwise it is excludable with gₙ ≡ q₀
-- statement:
--   Let $M$ be an $r\times s$ matrix ($r,s\ge1$) of probability distributions on a closed bounded convex $X\subseteq\mathbb R^N$, and for $q\in Q$ let $T(q)$ be the convex hull of the $r$ points $\sum_{j=1}^s q_j\bar m(i,j)$. Let $S\subseteq\mathbb R^N$ be closed and convex. Then
--
--   1. $S$ is approachable in $M$ if and only if $S\cap T(q)\neq\emptyset$ for every $q\in Q$;
--   2. if $S\cap T(q_0)=\emptyset$ for some $q_0\in Q$, then $S$ is excludable in $M$ with the stationary strategy $g_n\equiv q_0$.
--
--   In particular every closed convex set is either approachable or excludable. This is the paper's vector analogue of von Neumann's minimax theorem.
--
--   **Formalization Note** $S$ may be unbounded or empty (the empty set meets no $T(q)$, is not approachable because its distance is $+\infty$, and is excludable). $r,s\ge1$ is added so that both players have strategies; the approachability notion quantifies over all plays of the strategies, on every probability space in `Type`.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 6, THEOREM 3

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §3, p. 6, THEOREM 3: a closed convex set `S` is approachable if and only
if it intersects every set `T(q)`; if it fails to intersect `T(q₀)`, it is excludable with
`gₙ ≡ q₀`. -/
theorem convex_approachable_iff {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (S : Set (E N)) (hS : IsClosed S) (hSc : Convex ℝ S) :
    (G.ApproachableIn S ↔ ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) ∧
      ∀ (q₀ : Fin s → ℝ) (hq₀ : q₀ ∈ stdSimplex ℝ (Fin s)), S ∩ G.T q₀ = ∅ →
        G.ExcludableWith S (Strategy.const q₀ hq₀) := by sorry

end VectorPayoffs.Convex
