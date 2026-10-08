-- Prove2me | Theorems.Thm_TuranMatching_Clique_claim_2_3
-- name    : TuranMatching.Clique.claim_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:35.528997+00:00
-- url     : https://prove2.me/theorems/b09b167c-2f0f-43ae-9990-e640fe9a13bc
-- title:
--   Claim 2.3 — w.l.o.g. every component of $G-B$ has a vertex with no neighbour in the smallest class $B_k$
-- statement:
--   Throughout, $k\ge2$, $n\ge2s+1$, and $G$ is an **extremal** graph: a graph on $n$ vertices with clique number at most $k$ and matching number at most $s$ having the maximum possible number of edges among all such graphs. Let $B$ be an odd barrier of $G$ with value $s$ such that every two non-adjacent vertices of $B$ have the same neighbourhood. The pair $(G,B)$ maximizes the sum of squared sizes of the components of $G-B$ among all such extremal graph and barrier pairs.
--
--   Then, without loss of generality, every component of $G-B$ has a vertex with no neighbour in the smallest class of $G_B$. Precisely, there is a graph $G'$ on the same vertices such that
--
--   1. $G'$ is again extremal;
--   2. $G'$ and $G$ induce the same graph on the vertices outside $B$ (so $G'-B$ has the same components $A_1,\dots,A_m$), and the same graph on $B$;
--   3. every two non-adjacent vertices of $B$ have the same neighbourhood in $G'$;
--   4. there is a partition of $B$ into classes $B_1,\dots,B_k$ (possibly empty) with $uv\in E(G')\iff$ $u,v$ lie in different classes, for all $u,v\in B$, and a class $B_k$ of minimum size among them;
--   5. for every component $A_i$ of $G'-B$ there is a vertex $v_i\in A_i$ with no neighbour in $B_k$ in $G'$.
--
--   The modification changes only edges between the components and $B$; this is what the proof of Lemma 2.2 uses.
--
--   **Formalization Note** The paper's "without loss of generality" is stated existentially as the graph $G'$ with properties (1)–(5). The maximality hypothesis carries the opening assumption of §2; the unchanged graph outside $B$ preserves the sum of squares. The class labels are a map into `Fin k`, and the smallest class is a label `jk` whose class in $B$ has size at most that of every other label. The paper says "every $k$"; the restriction $k\ge2$ is needed because $G(n,k,s)$ has $k-1$ classes of total size $s$, which is impossible for $k=1$ and $s>0$, and no graph on $n\ge1$ vertices has clique number at most $0$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 3, Claim 2.3 (with the preceding sentence defining B_1, …, B_k)

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem claim_2_3 (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.IsExtremal (Admissible k s))
    (B : Finset (Fin n)) (hB : IsOddBarrier G B s)
    (hmax : ∀ (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (B' : Finset (Fin n)),
      G'.IsExtremal (Admissible k s) → IsOddBarrier G' B' s → compSqSum G' B' ≤ compSqSum G B)
    (hsame : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v → G.neighborSet u = G.neighborSet v) :
    ∃ (G' : SimpleGraph (Fin n)) (_ : DecidableRel G'.Adj) (cls : Fin n → Fin k) (jk : Fin k),
      G'.IsExtremal (Admissible k s) ∧
      G'.induce ((B : Set (Fin n))ᶜ) = G.induce ((B : Set (Fin n))ᶜ) ∧
      G'.induce (B : Set (Fin n)) = G.induce (B : Set (Fin n)) ∧
      (∀ u ∈ B, ∀ v ∈ B, ¬ G'.Adj u v → G'.neighborSet u = G'.neighborSet v) ∧
      (∀ u ∈ B, ∀ v ∈ B, G'.Adj u v ↔ cls u ≠ cls v) ∧
      (∀ j : Fin k, #{w ∈ B | cls w = jk} ≤ #{w ∈ B | cls w = j}) ∧
      ∀ c : (G'.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent,
        ∃ v ∈ c.supp, ∀ w ∈ B, cls w = jk → ¬ G'.Adj (v : Fin n) w := by sorry

end TuranMatching.Clique
