-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_line_graph_or_decomposes
-- name    : StrongPerfectGraph.LineGraph.line_graph_or_decomposes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:10.404482+00:00
-- url     : https://prove2.me/theorems/ac1c4a2f-37b9-4fec-87ba-82d8e267c61a
-- title:
--   5.4 (= 8.6), pp. 76 and 105 — a maximal appearance is all of G, or G decomposes
-- statement:
--   Let $G$ be a Berge graph and $J$ a $3$-connected graph such that there is no $J$-enlargement with a nondegenerate appearance in $G$. Let $L(H_0)$ be an appearance of $J$ in $G$ such that, if $L(H_0)$ is degenerate, then $H_0 = J = K_{3,3}$ and no $J$-enlargement appears in $\overline{G}$. Then either
--
--   1. $G = L(H_0)$, or
--   2. $H_0 \ne K_{3,3}$ and $G$ admits a proper 2-join, or
--   3. $G$ admits a balanced skew partition.
--
--   This is the general theorem of §§5–8 from which both 5.1 and 5.2 follow, by choosing $J$ maximal under enlargement.
--
--   **Formalization Note** The appearance is an induced embedding $e : L(H_0) \hookrightarrow G$, and "$G = L(H_0)$" says that $e$ is surjective. "$H_0 = J = K_{3,3}$" and "$H_0 \ne K_{3,3}$" are up to isomorphism.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 76, 5.4; restated and proved as 8.6, p. 105

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_Main_IsProperTwoJoin
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears

namespace StrongPerfectGraph.LineGraph

theorem line_graph_or_decomposes {V W U : Type*} [Fintype V] [Fintype W] [Fintype U]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (hmax : ¬ HasNondegenerateEnlargementAppearance J G)
    (H₀ : SimpleGraph U) (hsub : IsSubdivision J H₀) (hbip : H₀.IsBipartite)
    (e : H₀.lineGraph ↪g G)
    (hdeg : IsDegenerateAppearance J H₀ →
      IsK33 H₀ ∧ IsK33 J ∧ ¬ EnlargementAppears J Gᶜ) :
    Function.Surjective e ∨ (¬ IsK33 H₀ ∧ StrongPerfectGraph.Main.IsProperTwoJoin G) ∨
      StrongPerfectGraph.Main.AdmitsBalancedSkewPartition G := by sorry

end StrongPerfectGraph.LineGraph
