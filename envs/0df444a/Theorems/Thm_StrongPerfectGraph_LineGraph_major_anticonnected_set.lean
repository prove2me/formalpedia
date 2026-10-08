-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_major_anticonnected_set
-- name    : StrongPerfectGraph.LineGraph.major_anticonnected_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:38.391325+00:00
-- url     : https://prove2.me/theorems/94d716d9-9514-4cec-9d41-55cf7d4c0428
-- title:
--   6.1, pp. 85–86 — common neighbours of an anticonnected set of major vertices
-- statement:
--   Let $G$ be a Berge graph, let $L(H)$ be an appearance in $G$ of a $3$-connected graph $J$, and let $Y$ be an anticonnected set of major vertices (vertices outside $L(H)$ whose neighbourhood in $L(H)$ saturates $L(H)$). Assume that the set of all $Y$-complete vertices of $L(H)$ does not saturate $L(H)$. Then one of the following holds:
--
--   1. $J = K_{3,3}$ or $K_4$, and there is an overshadowed appearance of $J$ in $G$;
--   2. $J = K_{3,3}$ or $K_4$, $L(H)$ is degenerate, and there is an overshadowed appearance of $J$ in $\overline{G}$;
--   3. $J = K_{3,3}$, $L(H)$ is degenerate, and some $J$-enlargement appears in $\overline{G}$;
--   4. $J = K_4$ and $|V(H)| = 6$;
--   5. $J = K_4$, $L(H)$ is degenerate, and there are nonadjacent $y, y' \in Y$ with the following property. Let the $4$-cycle of $H$ formed by the branch-vertices have edges $a, b, c, d$ in order; let $p$ be the third edge of $H$ at the common end of $a, b$, and similarly $q$ for $b, c$, $r$ for $c, d$ and $s$ for $d, a$. Then, up to symmetry, the neighbours of $y$ in $L(H)$ are $a, b, d, q, r$ and possibly $c$, and the neighbours of $y'$ in $L(H)$ are $b, c, d, p, s$ and possibly $a$.
--
--   This is the main result of §6 on major attachments: apart from small exceptional configurations, every anticonnected set of major vertices has common neighbours that saturate $L(H)$.
--
--   **Formalization Note** "Up to symmetry" is rendered by quantifying existentially over the labelling: the branch-vertices $w_1, w_2, w_3, w_4$ with $a = w_1w_2$, $b = w_2w_3$, $c = w_3w_4$, $d = w_4w_1$ and the edges $p, q, r, s$ at $w_2, w_3, w_4, w_1$ may be chosen in any of the symmetric ways, and $y, y'$ in either order.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 85–86, 6.1

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
import Definitions.Def_StrongPerfectGraph_LineGraph_Saturates
import Definitions.Def_StrongPerfectGraph_LineGraph_Appears
import Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed

namespace StrongPerfectGraph.LineGraph

theorem major_anticonnected_set {V W U : Type*} [Fintype V] [Fintype W] [Fintype U]
    (G : SimpleGraph V) (hG : StrongPerfectGraph.Main.IsBerge G) (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (H : SimpleGraph U) (hsub : IsSubdivision J H) (hbip : H.IsBipartite)
    (e : H.lineGraph ↪g G) (Y : Set V) (hY : StrongPerfectGraph.Main.IsConnectedSet Gᶜ Y)
    (hmajor : ∀ y ∈ Y, y ∉ Set.range e ∧
      Saturates H {f | ∃ hf : f ∈ H.edgeSet, G.Adj y (e ⟨f, hf⟩)})
    (hnot : ¬ Saturates H {f | ∃ hf : f ∈ H.edgeSet, ∀ y ∈ Y, G.Adj y (e ⟨f, hf⟩)}) :
    ((IsK33 J ∨ IsK4 J) ∧ HasOvershadowedAppearance J G) ∨
    ((IsK33 J ∨ IsK4 J) ∧ IsDegenerateAppearance J H ∧ HasOvershadowedAppearance J Gᶜ) ∨
    (IsK33 J ∧ IsDegenerateAppearance J H ∧ EnlargementAppears J Gᶜ) ∨
    (IsK4 J ∧ Fintype.card U = 6) ∨
    (IsK4 J ∧ IsDegenerateAppearance J H ∧
      ∃ y ∈ Y, ∃ y' ∈ Y, ¬ G.Adj y y' ∧
        ∃ w₁ w₂ w₃ w₄ : U, [w₁, w₂, w₃, w₄].Nodup ∧
          IsBranchVertex H w₁ ∧ IsBranchVertex H w₂ ∧
          IsBranchVertex H w₃ ∧ IsBranchVertex H w₄ ∧
          H.Adj w₁ w₂ ∧ H.Adj w₂ w₃ ∧ H.Adj w₃ w₄ ∧ H.Adj w₄ w₁ ∧
          ∃ p q r s : Sym2 U,
            p ∈ H.incidenceSet w₂ ∧ p ≠ s(w₁, w₂) ∧ p ≠ s(w₂, w₃) ∧
            q ∈ H.incidenceSet w₃ ∧ q ≠ s(w₂, w₃) ∧ q ≠ s(w₃, w₄) ∧
            r ∈ H.incidenceSet w₄ ∧ r ≠ s(w₃, w₄) ∧ r ≠ s(w₄, w₁) ∧
            s ∈ H.incidenceSet w₁ ∧ s ≠ s(w₄, w₁) ∧ s ≠ s(w₁, w₂) ∧
            ({f | ∃ hf : f ∈ H.edgeSet, G.Adj y (e ⟨f, hf⟩)} =
                {s(w₁, w₂), s(w₂, w₃), s(w₄, w₁), q, r} ∨
              {f | ∃ hf : f ∈ H.edgeSet, G.Adj y (e ⟨f, hf⟩)} =
                {s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁), q, r}) ∧
            ({f | ∃ hf : f ∈ H.edgeSet, G.Adj y' (e ⟨f, hf⟩)} =
                {s(w₂, w₃), s(w₃, w₄), s(w₄, w₁), p, s} ∨
              {f | ∃ hf : f ∈ H.edgeSet, G.Adj y' (e ⟨f, hf⟩)} =
                {s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁), p, s})) := by sorry

end StrongPerfectGraph.LineGraph
