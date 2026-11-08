-- Prove2me | Theorems.Thm_StrongPerfectGraph_Main_minimum_imperfect_no_proper_homogeneous_pair
-- name    : StrongPerfectGraph.Main.minimum_imperfect_no_proper_homogeneous_pair
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T06:14:48.863041+00:00
-- url     : https://prove2.me/theorems/4b110f54-ecda-4576-94e2-127a21550028
-- title:
--   A minimum imperfect graph admits no proper homogeneous pair
-- statement:
--   Let $G$ be a minimum imperfect graph: a Berge graph that is not perfect, such that every Berge graph with fewer vertices is perfect. Then $G$ admits no proper homogeneous pair:
--
--   $$G\ \text{minimum imperfect}\ \Longrightarrow\ G\ \text{admits no proper homogeneous pair}.$$
--
--   Here a proper homogeneous pair is a pair $(A,B)$ of disjoint nonempty vertex sets such that, writing $A_1,A_2$ for the sets of $A$-complete and $A$-anticomplete vertices and $B_1,B_2$ similarly, we have $A_1\cup A_2=B_1\cup B_2=V(G)\setminus(A\cup B)$ and the four sets $A_1\cap B_1$, $A_1\cap B_2$, $A_2\cap B_1$, $A_2\cap B_2$ are all nonempty.
--
--   The paper attributes this to Chvátal and Sbihi (reference [7], *Bull-free Berge graphs are perfect*, Graphs Combin. 3 (1987), 127–139) in the proof of 1.2 assuming 1.3: "It is shown in [7] that G does not admit a proper homogeneous pair." It is one of the ingredients used to rule out every outcome of the decomposition theorem 1.3 for a minimum imperfect graph.
--
--   **Formalization Note** `IsMinimumImperfect` and `IsProperHomogeneousPair` are the mission definitions.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), 51-229, p. 56, proof of 1.2 assuming 1.3 ("It is shown in [7] that G does not admit a proper homogeneous pair"), citing Chvatal & Sbihi, Bull-free Berge graphs are perfect, Graphs Combin. 3 (1987) 127-139

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsMinimumImperfect
import Definitions.Def_StrongPerfectGraph_Main_IsProperHomogeneousPair

namespace StrongPerfectGraph.Main

/-- Chvátal–Sbihi: a minimum imperfect graph admits no proper homogeneous pair (p. 56). -/
theorem minimum_imperfect_no_proper_homogeneous_pair {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsMinimumImperfect G) : ¬ IsProperHomogeneousPair G := by sorry

end StrongPerfectGraph.Main
