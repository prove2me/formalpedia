-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_minimum_imperfect_no_proper_two_join
-- name    : StrongPerfectGraph.Main.minimum_imperfect_no_proper_two_join
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T06:14:48.572012+00:00
-- url     : https://prove2.me/theorems/580fd135-e19c-4618-b575-f11a6e8a5729
-- title:
--   A minimum imperfect graph admits no proper 2-join
-- statement:
--   Call a finite graph $G$ a *minimum imperfect graph* if it is Berge, not perfect, and every Berge graph with fewer vertices than $G$ is perfect (i.e. $G$ is a counterexample to the strong perfect graph theorem with as few vertices as possible). Then $G$ admits no proper 2-join:
--
--   $$G\ \text{minimum imperfect}\ \Longrightarrow\ G\ \text{admits no proper 2-join}.$$
--
--   Here a proper 2-join is a partition $(X_1,X_2)$ of $V(G)$ with disjoint nonempty $A_i,B_i\subseteq X_i$ such that $A_1$ is complete to $A_2$, $B_1$ is complete to $B_2$, there are no other edges between $X_1$ and $X_2$, every component of $G|X_i$ meets both $A_i$ and $B_i$, and if $|A_i|=|B_i|=1$ and $G|X_i$ is a path joining them then that path has odd length at least $3$.
--
--   The paper attributes this to Cornuéjols and Cunningham (reference [13], *Compositions for perfect graphs*, Discrete Math. 55 (1985), 245–254) in the proof of 1.2 assuming 1.3: "It is shown in [13] that G does not admit a proper 2-join." It is one of the ingredients used to rule out every outcome of the decomposition theorem 1.3 for a minimum imperfect graph.
--
--   **Formalization Note** `IsMinimumImperfect` and `IsProperTwoJoin` are the mission definitions; minimality quantifies over all Berge graphs on `Fin n` with `n` smaller than the number of vertices of $G$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), 51-229, p. 56, proof of 1.2 assuming 1.3 ("It is shown in [13] that G does not admit a proper 2-join"), citing Cornuejols & Cunningham, Compositions for perfect graphs, Discrete Math. 55 (1985) 245-254

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsMinimumImperfect
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin

namespace StrongPerfectGraph.Main

/-- Cornuéjols–Cunningham: a minimum imperfect graph admits no proper 2-join (p. 56). -/
theorem minimum_imperfect_no_proper_two_join {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsMinimumImperfect G) : ¬ IsProperTwoJoin G := by sorry

end StrongPerfectGraph.Main
