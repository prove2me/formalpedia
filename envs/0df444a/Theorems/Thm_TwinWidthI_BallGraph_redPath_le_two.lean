-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_redPath_le_two
-- name    : TwinWidthI.BallGraph.redPath_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:28.773526+00:00
-- url     : https://prove2.me/theorems/8dc5bce4-2285-4cf9-bcac-b05b4733810a
-- title:
--   §3, p. 3:12 — red paths have twin-width at most 2
-- statement:
--   For $n\ge 0$ let $P_n$ be the path on the vertices $0,1,\dots,n-1$, with $i$ adjacent to $i+1$, and let $P^r_n=(V(P_n),\emptyset,E(P_n))$ be the *red path*: the trigraph in which every edge of $P_n$ is red. Then
--   $$\operatorname{tww}(P^r_n)\le 2 .$$
--
--   This is the base case $d=1$ of Theorem 4.3: the $1$-dimensional $n$-grid is the path $P_n$.
--
--   **Formalization Note.** Red twin-width is the predicate `RedTwinWidthLE` of the Setting: a sequence of merges of parts from singletons to at most one part in which each part is joined by an edge of $P_n$ to at most $2$ other parts. The statement holds for every $n$, including $n=0,1$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:12, §3, "red paths have twin-width at most 2"; used as the base case of Theorem 4.3, p. 3:15

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- §3, p. 3:12: red paths have twin-width at most 2. -/
theorem redPath_le_two (n : ℕ) : RedTwinWidthLE (SimpleGraph.pathGraph n) 2 := by sorry

end TwinWidthI.BallGraph
