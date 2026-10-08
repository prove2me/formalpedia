-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_overshadowed_enlargement_or_balanced_skew_partition
-- name    : StrongPerfectGraph.LineGraph.overshadowed_enlargement_or_balanced_skew_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:27.562673+00:00
-- url     : https://prove2.me/theorems/5596b8d4-f922-44d8-915b-9674af72eead
-- title:
--   7.5, p. 94 — an overshadowed appearance yields an enlargement or a balanced skew partition
-- statement:
--   Let $G$ be a Berge graph, and let $L(H)$ be an overshadowed appearance of $J$ in $G$, where $J$ is $3$-connected. Then either
--
--   1. there is a $J$-enlargement with a nondegenerate appearance in $G$, or
--   2. $G$ admits a balanced skew partition.
--
--   This removes overshadowed appearances from the analysis of §8.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 94, 7.5

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears
import Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed

namespace StrongPerfectGraph.LineGraph

theorem overshadowed_enlargement_or_balanced_skew_partition {V W U : Type*}
    [Fintype V] [Fintype W] [Fintype U]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (H : SimpleGraph U) (hsub : IsSubdivision J H) (hbip : H.IsBipartite)
    (e : H.lineGraph ↪g G) (hov : IsOvershadowed H G e) :
    HasNondegenerateEnlargementAppearance J G ∨ StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.LineGraph
