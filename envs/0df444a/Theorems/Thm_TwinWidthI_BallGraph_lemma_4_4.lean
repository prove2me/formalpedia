-- Prove2me | Theorems.Thm_TwinWidthI_BallGraph_lemma_4_4
-- name    : TwinWidthI.BallGraph.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:35.904271+00:00
-- url     : https://prove2.me/theorems/3aba69f4-b13c-40e0-a257-aefedd2003f6
-- title:
--   Lemma 4.4, p. 3:15 — every subgraph of $K^r_{n,d}$ has twin-width at most $2(3^d-1)$
-- statement:
--   Let $d,n\ge 0$ and let $K_{n,d}$ be the $d$-dimensional $n$-grid with diagonals: the graph on $[n]^d$ in which distinct $x,y$ are adjacent if and only if $\max_i|x_i-y_i|\le 1$. Let $K^r_{n,d}=([n]^d,\emptyset,E(K_{n,d}))$ be the trigraph with only red edges. Every subgraph of $K^r_{n,d}$, that is, every trigraph $H^r=(S,\emptyset,E(H))$ with $S\subseteq[n]^d$ and $H$ a subgraph of $K_{n,d}[S]$, satisfies
--   $$\operatorname{tww}(H^r)\le 2(3^d-1).$$
--
--   This is the step from grids to unit ball graphs: in the proof of Theorem 4.5 the contracted ball graph is a subgraph of $K^r_{n,d}$.
--
--   **Formalization Note.** A subgraph of the all-red trigraph $K^r_{n,d}$ is all-red, so its twin-width is the predicate `RedTwinWidthLE` of the Setting, applied to $H$. The subtraction $3^d-1$ is in $\mathbb N$ and exact since $3^d\ge 1$. No hypothesis on $d,n$ is added: for $n=0$ or $d=0$ the graph has at most one vertex.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:15, Lemma 4.4

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting

namespace TwinWidthI.BallGraph

/-- Lemma 4.4, p. 3:15: every subgraph of the all-red trigraph `K^r_{n,d}` has twin-width at
most `2(3^d − 1)`. -/
theorem lemma_4_4 (d n : ℕ) (S : Finset (Fin d → Fin n)) (H : SimpleGraph S)
    (hH : H ≤ (kingGraph d n).induce (S : Set (Fin d → Fin n))) :
    RedTwinWidthLE H (2 * (3 ^ d - 1)) := by sorry

end TwinWidthI.BallGraph
