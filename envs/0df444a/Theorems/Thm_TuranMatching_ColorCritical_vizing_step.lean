-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_vizing_step
-- name    : TuranMatching.ColorCritical.vizing_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:34.226704+00:00
-- url     : https://prove2.me/theorems/5650217f-875b-400c-8a5a-1174dddb05ee
-- title:
--   Proof of Prop. 3.1, p. 5 — maximum degree ≤ 2s and matching number ≤ s give at most (2s+1)s edges (via Vizing)
-- statement:
--   Let $G$ be a finite graph in which every vertex has degree at most $2s$ and whose matching number is at most $s$. Then
--   $$|E(G)|\le (2s+1)\,s.$$
--
--   In the proof of Proposition 3.1 this is applied to the subgraph induced on the low-degree vertices $Y=V-X$. It bounds the number of edges not incident with the high-degree set $X$.
--
--   **Formalization Note** The page writes "the number of vertices in this induced subgraph is at most $(2s+1)s$"; the vertex count is not bounded (isolated vertices are unconstrained), and the bound the argument gives and uses is on edges. The statement is posed for a graph on an arbitrary finite vertex type, so that it applies directly to an induced subgraph.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, third paragraph, second sentence

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem vizing_step {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : ℕ) (hdeg : ∀ v, G.degree v ≤ 2 * s) (hG : TuranMatching.Clique.matchingNumber G ≤ s) :
    #G.edgeFinset ≤ (2 * s + 1) * s := by sorry

end TuranMatching.ColorCritical
