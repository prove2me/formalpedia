-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_double_split_perfect
-- name    : StrongPerfectGraph.Main.double_split_perfect
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T06:17:14.126924+00:00
-- url     : https://prove2.me/theorems/525d85e3-665b-4f47-a672-29fd9dc350db
-- title:
--   Double split graphs are perfect
-- statement:
--   Let $m,n\ge 2$ and let $G$ be a double split graph: $V(G)$ is partitioned into $\{a_1,\dots,a_m\}$, $\{b_1,\dots,b_m\}$, $\{c_1,\dots,c_n\}$, $\{d_1,\dots,d_n\}$, where
--
--   1. $a_i$ is adjacent to $b_i$ for every $i$, and $c_j$ is nonadjacent to $d_j$ for every $j$;
--   2. there are no edges between $\{a_i,b_i\}$ and $\{a_{i'},b_{i'}\}$ for $i\ne i'$, and all four edges between $\{c_j,d_j\}$ and $\{c_{j'},d_{j'}\}$ for $j\ne j'$;
--   3. for every $i,j$ there are exactly two edges between $\{a_i,b_i\}$ and $\{c_j,d_j\}$, and these two edges have no common end.
--
--   Then $G$ is perfect:
--
--   $$\chi(G|X)=\omega(G|X)\qquad\text{for every } X\subseteq V(G).$$
--
--   The paper says "for double split graphs we leave it to the reader" when asserting that all basic graphs are perfect (p. 53). It is the double-split case of that assertion.
--
--   **Formalization Note** `IsDoubleSplit` is the mission definition: an equivalence $((\mathrm{Fin}\,m\times\mathrm{Bool})\sqcup(\mathrm{Fin}\,n\times\mathrm{Bool}))\simeq V$ labels $a_i,b_i$ as `inl (i,false)`, `inl (i,true)` and $c_j,d_j$ as `inr (j,false)`, `inr (j,true)`.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), 51-229, p. 52 (definition of double split graph) and p. 53 ("for double split graphs we leave it to the reader")

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

namespace StrongPerfectGraph.Main

/-- Double split graphs are perfect (p. 53, "left to the reader"). -/
theorem double_split_perfect {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsDoubleSplit G) : IsPerfect G := by sorry

end StrongPerfectGraph.Main
