-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_theorem_4_3_red
-- name    : TwinWidthI.BallGraph.theorem_4_3_red
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:01.38582+00:00
-- url     : https://prove2.me/theorems/d2f9e816-fe12-4ae6-b83d-be985ddde335
-- title:
--   Proof of Theorem 4.3, p. 3:15 — the all-red grid $R^d_n$ has twin-width at most $3d$
-- statement:
--   Let $d,n\ge 1$ and let $R^d_n=(V(P^d_n),\emptyset,E(P^d_n))$ be the trigraph on the vertex set $[n]^d$ of the $d$-dimensional $n$-grid whose edges, those of $P^d_n$ (pairs $x,y$ with $\sum_i|x_i-y_i|=1$), are all red. Then
--   $$\operatorname{tww}(R^d_n)\le 3d .$$
--
--   This is what the proof of Theorem 4.3 establishes, by induction on $d$; it implies Theorem 4.3 and the bound for every subgraph of the grid, and its argument is the one Lemma 4.4 follows.
--
--   **Formalization Note.** $[n]^d$ is `Fin d → Fin n`. The hypotheses $1\le d$ and $1\le n$ are the page's "positive integers $d$ and $n$". Red twin-width is `RedTwinWidthLE` of the Setting.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:15, proof of Theorem 4.3, "We will prove, by induction on d, that R^d_n has twin-width at most 3d"

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- Proof of Theorem 4.3, p. 3:15: the all-red trigraph `R^d_n` of the d-dimensional n-grid has
twin-width at most `3d`. -/
theorem theorem_4_3_red (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    RedTwinWidthLE (grid d n) (3 * d) := by sorry

end TwinWidthI.BallGraph
