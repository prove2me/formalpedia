-- Prove2me | Theorems.Thm_StrongPerfectGraph_EvenPrism_major_even_prism_skew_partition
-- name    : StrongPerfectGraph.EvenPrism.major_even_prism_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:28:03.003997+00:00
-- url     : https://prove2.me/theorems/4f128fa8-d4fc-485d-8996-ad722b6a3753
-- title:
--   10.5 — a major vertex forces a balanced skew partition
-- statement:
--   Let $G$ be a Berge graph with no nondegenerate appearance of $K_4$. If $G$ contains an even prism with a vertex major with respect to it, then
--
--   $$G\text{ admits a balanced skew partition}. $$
--
--   This isolates the major-vertex case of the even-prism decomposition.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 123, 10.5

import Definitions.Def_StrongPerfectGraph_EvenPrism_Prism
import Definitions.Def_StrongPerfectGraph_EvenPrism_Decompositions
import Definitions.Def_StrongPerfectGraph_EvenPrism_Appearance

namespace StrongPerfectGraph.EvenPrism

theorem major_even_prism_skew_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G)
    (hK4 : ¬ HasNondegenerateAppearanceK4 G)
    (a b : Fin 3 → V) (R : Fin 3 → List V)
    (hR : IsEvenPrism G a b R)
    (v : V) (hv : IsMajor G a b v) :
    StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.EvenPrism
