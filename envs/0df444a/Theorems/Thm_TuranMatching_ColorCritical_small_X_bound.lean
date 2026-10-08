-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_small_X_bound
-- name    : TuranMatching.ColorCritical.small_X_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:11.649001+00:00
-- url     : https://prove2.me/theorems/d5dec622-8297-4f98-82e0-83cf95dc46f6
-- title:
--   Proof of Prop. 3.1, p. 5 — if fewer than s vertices have degree > 2s, then G has fewer than (s−1)n + 2(s+1)s edges
-- statement:
--   Let $s\ge 1$ and let $G$ be a graph on $n$ vertices with matching number $\nu(G)\le s$. Let $X$ be the set of vertices of degree exceeding $2s$. If $|X|<s$, then
--   $$|E(G)|<(s-1)\,n+2(s+1)\,s.$$
--
--   This is the case of the proof of Proposition 3.1 in which there are too few high-degree vertices; combined with the comparison of this bound with $g(n,k,s)$, it shows that an extremal graph has exactly $s$ vertices of degree exceeding $2s$.
--
--   **Formalization Note** The hypothesis $s\ge 1$ keeps the natural-number subtraction $s-1$ honest; on the page $s>s_0(H)\ge 0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, third paragraph, third sentence

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem small_X_bound {n : ℕ} (s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hs : 1 ≤ s) (hG : TuranMatching.Clique.matchingNumber G ≤ s) (hX : #(highDeg G s) < s) :
    #G.edgeFinset < (s - 1) * n + 2 * (s + 1) * s := by sorry

end TuranMatching.ColorCritical
