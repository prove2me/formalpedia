-- Prove2me | Theorems.Thm_TuranMatching_ColorCritical_bigGraph_colorable_matching
-- name    : TuranMatching.ColorCritical.bigGraph_colorable_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:46.742534+00:00
-- url     : https://prove2.me/theorems/31d90ab0-39b6-4f70-8399-e453912cada2
-- title:
--   Proof of Prop. 3.1, p. 5 — G(n,k,s) is k-colorable, hence H-free when χ(H)=k+1, and has matching number s
-- statement:
--   Let $k\ge 2$ and $n\ge 2s$, and let $G(n,k,s)$ be the complete $k$-partite graph on $n$ vertices with $k-1$ balanced classes of total size $s$ and one class of size $n-s$. Then:
--
--   1. $G(n,k,s)$ is properly $k$-colorable;
--   2. its matching number is exactly $s$:
--   $$\nu\big(G(n,k,s)\big)=s;$$
--   3. for every graph $H$ of chromatic number $k+1$, $G(n,k,s)$ contains no subgraph isomorphic to $H$.
--
--   Consequently $G(n,k,s)$, with its $g(n,k,s)$ edges, is an admissible graph in Proposition 3.1, and $g(n,k,s)$ is a lower bound for the maximum there.
--
--   **Formalization Note** The page says "$k$ chromatic"; the Lean states $k$-colorability, which is what the argument uses (chromatic number exactly $k$ would additionally need $s\ge k-1$). The hypothesis $n\ge 2s$ is implicit on the page: the large class must have at least $s$ vertices for a matching of size $s$ to exist. "$H$-free" means no (not necessarily induced) subgraph copy of $H$ (Mathlib's `SimpleGraph.Free`). The vertex type of $H$ is any type in the lowest universe.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 5, proof of Proposition 3.1, first two sentences

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

open Finset SimpleGraph

namespace TuranMatching.ColorCritical

theorem bigGraph_colorable_matching (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s ≤ n) :
    (TuranMatching.Clique.bigGraph n k s).Colorable k ∧ TuranMatching.Clique.matchingNumber (TuranMatching.Clique.bigGraph n k s) = s ∧
      ∀ (W : Type) (H : SimpleGraph W), H.chromaticNumber = ((k + 1 : ℕ) : ℕ∞) →
        H.Free (TuranMatching.Clique.bigGraph n k s) := by sorry

end TuranMatching.ColorCritical
