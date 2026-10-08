-- Prove2me | Theorems.Thm_TuranMatching_Clique_induced_complete_k_partite
-- name    : TuranMatching.Clique.induced_complete_k_partite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:52.297086+00:00
-- url     : https://prove2.me/theorems/acb93721-f184-48c4-aa61-a83521deec2f
-- title:
--   Proof of Lemma 2.2, p. 3 — if non-adjacent vertices of $B$ share neighbourhoods and $G$ is $K_{k+1}$-free, $G_B$ is complete $k$-partite
-- statement:
--   Let $k\ge2$, let $G$ be a graph on $n$ vertices with no clique on $k+1$ vertices, and let $B$ be a set of vertices such that every two non-adjacent vertices of $B$ have the same neighbourhood in $G$. Then the induced subgraph $G_B$ is complete $k$-partite: there is a map $\mathrm{cls}$ from the vertices to $\{1,\dots,k\}$ such that for all $u,v\in B$,
--   $$uv\in E(G)\iff \mathrm{cls}(u)\ne\mathrm{cls}(v).$$
--
--   Some of the $k$ classes may be empty, as the paper allows. This is the first step of the proof of Lemma 2.2.
--
--   **Formalization Note** The classes are encoded by a map into `Fin k`; its values outside $B$ are irrelevant. The hypothesis $k\ge2$ is the standing restriction of the formalization (some $k\ge1$ is needed for a map into $\{1,\dots,k\}$ to exist).
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 3, proof of Lemma 2.2, first two sentences

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem induced_complete_k_partite (n k : ℕ) (hk : 2 ≤ k)
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree (k + 1)) (B : Finset (Fin n))
    (hsame : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v → G.neighborSet u = G.neighborSet v) :
    ∃ cls : Fin n → Fin k, ∀ u ∈ B, ∀ v ∈ B, G.Adj u v ↔ cls u ≠ cls v := by sorry

end TuranMatching.Clique
