-- Prove2me | Theorems.Thm_StrongPerfectGraph_DoubleSplit_maximal_striation_vertex
-- name    : StrongPerfectGraph.DoubleSplit.maximal_striation_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:39.206478+00:00
-- url     : https://prove2.me/theorems/67ddf9a7-4214-40f1-bac1-02e4e2ce07a5
-- title:
--   9.4, p. 112 — a vertex outside a maximal striation has a local or resolving neighbourhood
-- statement:
--   Let $G$ be a Berge graph such that no $K_4$-enlargement appears in $G$ or in $\overline{G}$ and there is no overshadowed appearance of $K_4$ in $G$ or in $\overline{G}$. Let $L$ be a maximal striation in $G$, let $f \in V(G) \setminus V(L)$, and let $X = N(f) \cap V(L)$. Then
--
--   $$X \text{ is local with respect to } L \quad\text{or}\quad X \text{ resolves } L.$$
--
--   In the proof of 9.6 this splits the vertices outside $V(L)$ into two classes, those with local and those with resolving neighbourhoods.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 112, 9.4

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears
import Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed
import Definitions.Def_StrongPerfectGraph_DoubleSplit_IsStriation

namespace StrongPerfectGraph.DoubleSplit

/-- 9.4 (p. 112): in a Berge graph `G` in which no `K₄`-enlargement appears in `G` or `G̅` and
there is no overshadowed appearance of `K₄` in `G` or `G̅`, the neighbour set in `V(L)` of a vertex
outside a maximal striation `L` is local with respect to `L` or resolves `L`. -/
theorem maximal_striation_vertex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : StrongPerfectGraph.Main.IsBerge G)
    (hEnl : ¬ StrongPerfectGraph.LineGraph.EnlargementAppears (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.EnlargementAppears (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (hOv : ¬ StrongPerfectGraph.LineGraph.HasOvershadowedAppearance (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.HasOvershadowedAppearance (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (L : Striation V) (hL : IsMaximalStriation G L) (f : V) (hf : f ∉ L.verts) :
    IsLocalForStriation G L {v | v ∈ L.verts ∧ G.Adj f v} ∨
      ResolvesStriation G L {v | v ∈ L.verts ∧ G.Adj f v} := by sorry

end StrongPerfectGraph.DoubleSplit
