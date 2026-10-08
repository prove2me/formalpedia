-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_low_degree_independent
-- name    : TuranMatching.ColorCritical.low_degree_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:02.505027+00:00
-- url     : https://prove2.me/theorems/e5bda6fb-486e-43a7-8737-0da7b89418d5
-- title:
--   Proof of Prop. 3.1, p. 5 — if exactly s vertices have degree > 2s, the remaining vertices form an independent set
-- statement:
--   Let $G$ be a graph on $n$ vertices with matching number $\nu(G)\le s$, and let $X$ be the set of vertices of degree exceeding $2s$. If $|X|=s$, then $Y=V-X$ is an independent set in $G$: for all vertices $y,z$,
--   $$y\notin X,\ z\notin X\ \Longrightarrow\ yz\notin E(G).$$
--
--   This structural step shows that, in the remaining case of the proof of Proposition 3.1, every edge of $G$ meets $X$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, fourth paragraph

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem low_degree_independent {n : ℕ} (s : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : TuranMatching.Clique.matchingNumber G ≤ s) (hX : #(highDeg G s) = s) :
    ∀ y z : Fin n, y ∉ highDeg G s → z ∉ highDeg G s → ¬ G.Adj y z := by sorry

end TuranMatching.ColorCritical
