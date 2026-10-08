-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_edge_set_without_even_track
-- name    : StrongPerfectGraph.LineGraph.edge_set_without_even_track
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:48:40.448347+00:00
-- url     : https://prove2.me/theorems/0f6cf314-7930-41c2-8b4d-d21b377d52d8
-- title:
--   5.7, pp. 77–78 — edge sets of a cyclically 3-connected bipartite graph with no even track between them
-- statement:
--   Let $H$ be a bipartite, cyclically $3$-connected graph, and let $X \subseteq E(H)$ be such that there is no track in $H$ of even length at least $4$ whose two end-edges are in $X$ and none of whose other edges is in $X$. Then one of the following holds:
--
--   1. $X$ saturates $L(H)$;
--   2. there is a branch-vertex $b$ of $H$ with $X \subseteq \delta(b)$;
--   3. there is a branch $B$ of $H$ with $X \subseteq E(B)$;
--   4. there is a branch $B$ of $H$ with ends $b_1, b_2$ such that $X \setminus E(B) = \delta(b_1) \setminus E(B)$;
--   5. there is a branch $B$ of $H$ of odd length with ends $b_1, b_2$ such that $X \setminus E(B) = (\delta(b_1) \cup \delta(b_2)) \setminus E(B)$;
--   6. there are two vertices $c_1, c_2$ of $H$, of different biparity (every track between them is odd) and not in the same branch of $H$, such that $X = \delta(c_1) \cup \delta(c_2)$.
--
--   In particular, either statement 1 or 6 holds, or at most two branch-vertices of $H$ are incident with more than one edge of $X$, and exactly two only if statement 5 holds.
--
--   This lemma classifies the neighbourhood, inside an appearance $L(H)$, of a vertex of a Berge graph: it is the tool behind the analysis of single attachments and of strip systems.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 77–78, 5.7

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision
import Definitions.Def_StrongPerfectGraph_LineGraph_Saturates

namespace StrongPerfectGraph.LineGraph

theorem edge_set_without_even_track {U : Type*} [Fintype U] (H : SimpleGraph U)
    (hbip : H.IsBipartite) (hcyc : IsCyclicallyThreeConnected H)
    (X : Set (Sym2 U)) (hX : X ⊆ H.edgeSet)
    (hno : ∀ p : List U, IsTrack H p → Even (p.length - 1) → 4 ≤ p.length - 1 →
      ∀ f g : Sym2 U, (trackEdgeList p).head? = some f → (trackEdgeList p).getLast? = some g →
        f ∈ X → g ∈ X → ∃ h ∈ (trackEdgeList p).tail.dropLast, h ∈ X) :
    (Saturates H X ∨
      (∃ b : U, IsBranchVertex H b ∧ X ⊆ H.incidenceSet b) ∨
      (∃ B : List U, IsBranch H B ∧ X ⊆ trackEdges B) ∨
      (∃ (B : List U) (b₁ b₂ : U), IsBranch H B ∧ B.head? = some b₁ ∧ B.getLast? = some b₂ ∧
        X \ trackEdges B = H.incidenceSet b₁ \ trackEdges B) ∨
      (∃ (B : List U) (b₁ b₂ : U), IsBranch H B ∧ Odd (B.length - 1) ∧
        B.head? = some b₁ ∧ B.getLast? = some b₂ ∧
        X \ trackEdges B = (H.incidenceSet b₁ ∪ H.incidenceSet b₂) \ trackEdges B) ∨
      (∃ c₁ c₂ : U,
        (∀ p : List U, IsTrack H p → p.head? = some c₁ → p.getLast? = some c₂ →
          Odd (p.length - 1)) ∧
        (¬ ∃ B : List U, IsBranch H B ∧ c₁ ∈ B ∧ c₂ ∈ B) ∧
        X = H.incidenceSet c₁ ∪ H.incidenceSet c₂)) ∧
    (Saturates H X ∨
      (∃ c₁ c₂ : U,
        (∀ p : List U, IsTrack H p → p.head? = some c₁ → p.getLast? = some c₂ →
          Odd (p.length - 1)) ∧
        (¬ ∃ B : List U, IsBranch H B ∧ c₁ ∈ B ∧ c₂ ∈ B) ∧
        X = H.incidenceSet c₁ ∪ H.incidenceSet c₂) ∨
      ({b : U | IsBranchVertex H b ∧ 1 < (H.incidenceSet b ∩ X).ncard}.ncard ≤ 2 ∧
        ({b : U | IsBranchVertex H b ∧ 1 < (H.incidenceSet b ∩ X).ncard}.ncard = 2 →
          ∃ (B : List U) (b₁ b₂ : U), IsBranch H B ∧ Odd (B.length - 1) ∧
            B.head? = some b₁ ∧ B.getLast? = some b₂ ∧
            X \ trackEdges B = (H.incidenceSet b₁ ∪ H.incidenceSet b₂) \ trackEdges B))) := by sorry

end StrongPerfectGraph.LineGraph
