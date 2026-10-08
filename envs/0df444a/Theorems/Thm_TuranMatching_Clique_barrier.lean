-- Prove2me | Theorems.Thm_TuranMatching_Clique_barrier
-- name    : TuranMatching.Clique.barrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:43.755169+00:00
-- url     : https://prove2.me/theorems/5eed525d-b738-4b2a-bd73-f2953a7d01ab
-- title:
--   §2, p. 2 — Tutte–Berge/Gallai–Edmonds: a barrier $B$ with all components of $G-B$ odd and $|B|+\sum(a_i-1)/2=\nu(G)$
-- statement:
--   Let $G$ be a graph on $n$ vertices with matching number $\nu(G)$. Then there is a set $B$ of vertices such that every connected component $A_1,\dots,A_m$ of $G-B$ has an odd number of vertices $a_i=|A_i|$, and
--   $$|B|+\sum_{i=1}^{m}\frac{a_i-1}{2}=\nu(G).$$
--
--   This is the form of the Tutte–Berge / Gallai–Edmonds theorem used at the start of the proof of Theorem 1.1. It holds, for instance, for a maximal barrier, all of whose components are factor-critical.
--
--   **Formalization Note** The paper writes $s$ on the right-hand side, for an extremal graph whose matching number equals $s$; the statement here is the general theorem it cites, with $\nu(G)$ in place of $s$. The second relation of the page, $|B|+\sum a_i=n$, holds automatically because the components partition the vertices outside $B$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 2, §2, second sentence (Tutte–Berge / Edmonds–Gallai, cf. Lovász–Plummer [2])

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TuranMatching.Clique

theorem barrier (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ B : Finset (Fin n), IsOddBarrier G B (matchingNumber G) := by sorry

end TuranMatching.Clique
