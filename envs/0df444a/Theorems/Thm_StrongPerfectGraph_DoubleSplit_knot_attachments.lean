-- Prove2me | Theorems.Thm_StrongPerfectGraph_DoubleSplit_knot_attachments
-- name    : StrongPerfectGraph.DoubleSplit.knot_attachments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:29:35.561714+00:00
-- url     : https://prove2.me/theorems/a9c6ee56-04be-40df-8713-623bb6ebee96
-- title:
--   9.3, p. 109 — attachments of a connected set to a knot
-- statement:
--   Let $(P_1, P_2, Q_1, Q_2)$ be a knot in a Berge graph $G$, inducing $K$. Assume that no $K_4$-enlargement appears in $G$ or in $\overline{G}$, and that there is no overshadowed appearance of $K_4$ in $G$ or in $\overline{G}$. Let $F \subseteq V(G) \setminus V(K)$ be connected, such that its set of attachments in $K$ is not local. Then one of the following holds:
--
--   1. some vertex of $F$ has a neighbour set in $K$ that resolves the knot;
--   2. (up to symmetry) there is a path $R$ in $F$ with ends $r_1, r_2$ such that $r_1, a_1$ have the same neighbours in $V(P_2) \cup V(Q_1) \cup V(Q_2)$, there are no edges between $R \setminus r_1$ and $V(P_2) \cup V(Q_1) \cup V(Q_2)$, $r_2$ has a neighbour in $P_1 \setminus a_1$, and there are no edges between $R \setminus r_2$ and $P_1 \setminus a_1$;
--   3. (up to symmetry) there is an odd path $R$ in $F$ with ends $r_1, r_2$ such that $r_1, a_1$ and $r_2, b_1$ have the same neighbours in $V(P_2) \cup V(Q_1) \cup V(Q_2)$, there are no edges between $R^*$ and $V(P_2) \cup V(Q_1) \cup V(Q_2)$, and no edges between $R$ and $P_1$ except possibly $r_1a_1$ and $r_2b_1$;
--   4. (up to symmetry) there is $f \in F$ such that $f, x_1$ have the same neighbours in $V(P_1) \cup V(P_2) \cup V(Q_2)$ and $f$ is not adjacent to $y_1$.
--
--   This lemma unifies the attachment analysis of 5.8 and 6.1 for degenerate appearances of $K_4$ and is the engine of 9.4 and 9.5.
--
--   **Formalization Note** "Up to symmetry" means: for the knot as labelled, or for one of the three relabelled quadruples listed in the definition `KnotOutcomes` (exchange of $P_1, P_2$ and $Q_1, Q_2$ with the two compatible renamings of the ends, and their composite, the reversal of all four).
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 109, 9.3 (with the meaning of "up to symmetry" stated just before it)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears
import Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed
import Definitions.Def_StrongPerfectGraph_DoubleSplit_IsKnot
import Definitions.Def_StrongPerfectGraph_DoubleSplit_KnotOutcomes

namespace StrongPerfectGraph.DoubleSplit

/-- 9.3 (p. 109). Let `(P₁, P₂, Q₁, Q₂)` be a knot in a Berge graph `G`, inducing `K`. Assume that
no `K₄`-enlargement appears in `G` or in `G̅`, and that there is no overshadowed appearance of `K₄`
in `G` or in `G̅`. Let `F ⊆ V(G) \ V(K)` be connected with its set of attachments in `K` not local.
Then some vertex of `F` has a neighbour set in `K` resolving the knot, or (up to symmetry) outcome
2, or (up to symmetry) outcome 3, or (up to symmetry) outcome 4 holds. -/
theorem knot_attachments {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : StrongPerfectGraph.Main.IsBerge G) (P₁ P₂ Q₁ Q₂ : List V) (hK : IsKnot G P₁ P₂ Q₁ Q₂)
    (hEnl : ¬ StrongPerfectGraph.LineGraph.EnlargementAppears (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.EnlargementAppears (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (hOv : ¬ StrongPerfectGraph.LineGraph.HasOvershadowedAppearance (⊤ : SimpleGraph (Fin 4)) G ∧
      ¬ StrongPerfectGraph.LineGraph.HasOvershadowedAppearance (⊤ : SimpleGraph (Fin 4)) Gᶜ)
    (F : Set V) (hFconn : StrongPerfectGraph.Main.IsConnectedSet G F) (hFdisj : Disjoint F (knotVerts P₁ P₂ Q₁ Q₂))
    (hFnl : ¬ IsLocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G (knotVerts P₁ P₂ Q₁ Q₂) F)) :
    (∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ {v | v ∈ knotVerts P₁ P₂ Q₁ Q₂ ∧ G.Adj f v}) ∨
    UpToKnotSymmetry (fun A B C D => KnotOutcome2 G A B C D F) P₁ P₂ Q₁ Q₂ ∨
    UpToKnotSymmetry (fun A B C D => KnotOutcome3 G A B C D F) P₁ P₂ Q₁ Q₂ ∨
    UpToKnotSymmetry (fun A B C D => KnotOutcome4 G A B C D F) P₁ P₂ Q₁ Q₂ := by sorry

end StrongPerfectGraph.DoubleSplit
