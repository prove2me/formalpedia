-- Prove2me | Theorems.Thm_StrongPerfectGraph_DoubleSplit_maximal_striation_connected
-- name    : StrongPerfectGraph.DoubleSplit.maximal_striation_connected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:35.813795+00:00
-- url     : https://prove2.me/theorems/061e7a38-6c54-4ed9-a57d-5910a784f460
-- title:
--   9.5, p. 113 — connected sets of local vertices attach locally to a maximal striation
-- statement:
--   Let $G$ be a Berge graph such that no $K_4$-enlargement appears in $G$ or in $\overline{G}$ and there is no overshadowed appearance of $K_4$ in $G$ or in $\overline{G}$. Let $L$ be a maximal striation in $G$ and let $F \subseteq V(G) \setminus V(L)$ be connected, such that for each $f \in F$ the set of neighbours of $f$ in $V(L)$ is local with respect to $L$. Then
--
--   $$\{v \in V(L) : v \text{ has a neighbour in } F\} \ \text{is local with respect to } L.$$
--
--   Together with 9.4 this controls how the components outside a maximal striation attach to it, which yields the decompositions in 9.6.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 113, 9.5

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears
import Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed
import Definitions.Def_StrongPerfectGraph_DoubleSplit_IsKnot
import Definitions.Def_StrongPerfectGraph_DoubleSplit_IsStriation

namespace StrongPerfectGraph.DoubleSplit

/-- 9.5 (p. 113): under the hypotheses of 9.4, if `F ⊆ V(G) \ V(L)` is connected and every
`f ∈ F` has a neighbour set in `V(L)` that is local with respect to the maximal striation `L`, then
the set of attachments of `F` in `V(L)` is local with respect to `L`. -/
theorem maximal_striation_connected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : StrongPerfectGraph.Main.IsBerge G)
    (hEnl : ¬ StrongPerfectGraph.LineGraph.EnlargementAppears (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.EnlargementAppears (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (hOv : ¬ StrongPerfectGraph.LineGraph.HasOvershadowedAppearance (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.HasOvershadowedAppearance (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (L : Striation V) (hL : IsMaximalStriation G L)
    (F : Set V) (hFdisj : Disjoint F L.verts) (hFconn : StrongPerfectGraph.Main.IsConnectedSet G F)
    (hFloc : ∀ f ∈ F, IsLocalForStriation G L {v | v ∈ L.verts ∧ G.Adj f v}) :
    IsLocalForStriation G L (attachments G L.verts F) := by sorry

end StrongPerfectGraph.DoubleSplit
