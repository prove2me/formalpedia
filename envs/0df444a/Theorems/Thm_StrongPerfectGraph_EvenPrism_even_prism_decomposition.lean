-- Prove2me | Theorems.Thm_StrongPerfectGraph_EvenPrism_even_prism_decomposition
-- name    : StrongPerfectGraph.EvenPrism.even_prism_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:28:10.753964+00:00
-- url     : https://prove2.me/theorems/10692d8d-a3f1-494a-9465-011c3f5e7994
-- title:
--   10.6 — even-prism decomposition
-- statement:
--   Let $G$ be a finite simple Berge graph with no nondegenerate appearance of $K_4$. If $G$ contains an even prism, then
--
--   $$\bigl(G\text{ is an even prism and }|V(G)|=9\bigr)\quad\text{or}\quad G\text{ admits a proper 2-join or a balanced skew partition}. $$
--
--   The first outcome identifies the entire graph: the existence of a nine-vertex induced prism alone is insufficient. This is Theorem 10.6, the even-prism step of the strong perfect graph theorem.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 124, 10.6 (restating 1.8.4)

import Definitions.Def_StrongPerfectGraph_EvenPrism_Prism
import Definitions.Def_StrongPerfectGraph_EvenPrism_Decompositions
import Definitions.Def_StrongPerfectGraph_EvenPrism_Appearance

namespace StrongPerfectGraph.EvenPrism

theorem even_prism_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G)
    (hK4 : ¬ HasNondegenerateAppearanceK4 G)
    (hP : ContainsEvenPrism G) :
    (IsEvenPrismGraph G ∧ Fintype.card V = 9) ∨
    AdmitsProperTwoJoin G ∨ StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.EvenPrism
