-- Prove2me | Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_14_expansion
-- name    : PathsTreesFlowers.Invariance.lemma_4_14_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:44.152503+00:00
-- url     : https://prove2.me/theorems/43f06126-a73c-4e5c-8770-8f6ef46b6434
-- title:
--   4.14, second statement, p. 458, with the choice used in 6.5 — a matching of G₂ extends through the complete expansion of a pseudovertex
-- statement:
--   Let $G$ be a finite graph and $\mathcal P_2$ a partition of its vertices; write $G_2 = G/\mathcal P_2$. Let $U$ be a part of $\mathcal P_2$ obtained by successively shrinking odd circuits (an odd-circuit set), so that $p = U$ is a pseudovertex of $G_2$ whose complete expansion is $U^+$. Let $\mathcal P_1$ be the partition obtained from $\mathcal P_2$ by splitting $U$ into single vertices, so that $G_1 = G/\mathcal P_1$ is the graph obtained from $G_2$ by completely expanding $p$. Let $M_2$ be any matching of $G_2$. Then:
--
--   1. there is a matching $M_P$ of $U^+$ leaving exactly one vertex of $U$ exposed such that
--   $$M_P \cup M_2 \text{ is a matching of } G_1;$$
--   2. if moreover no edge of $M_2$ meets $p$, then for every $u \in U$ the matching $M_P$ can be chosen to leave exactly $u$ exposed in $U$.
--
--   Since $|M_P| = (|U|-1)/2$ does not depend on $M_2$, any augmentation in $G_2$ yields a corresponding augmentation in $G_1$. Part 2 is the choice made in the proof of 6.5 ("If $u^*$ is pseudo, then by (4.14) $M'$ can be chosen so that $u$ is exposed in the expansion").
--
--   **Formalization Note** Edges keep their identity under shrinking, so the edges of $G_1$ and $G_2$ are subtypes of the edges of $G$; "$M_P \cup M_2$ is a matching of $G_1$" says there is a matching $M_1$ of $G_1$ whose underlying edges of $G$ are exactly $M_P \cup M_2$. "$M_2$ meets $p$" means $p$ is an end-point of an edge of $M_2$ in $G_2$.
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 458, 4.14, second statement (italic paragraph after 'Applying the above matching operation…'); p. 465, 6.5 (choice of the exposed vertex)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink

namespace PathsTreesFlowers.Invariance

open EdmondsMatching65.Polyhedron (IsMatching)

/-- 4.14, second statement, p. 458, with the choice used in 6.5 (p. 465). Let `G₂ = shrink G P₂`
and let `U` be a part of `P₂` obtained by successively shrinking odd circuits (the complete
expansion of the pseudovertex `p = U`), and let `P₁` be `P₂` with `U` split into singletons, so
that `G₁ = shrink G P₁` is obtained from `G₂` by completely expanding `p`. For every matching
`M₂` of `G₂` there is a matching `M_P` of `U⁺` leaving exactly one vertex of `U` exposed such that
`M_P ∪ M₂` is a matching of `G₁`; and if no edge of `M₂` meets `p`, the exposed vertex of `U` can
be any prescribed `u ∈ U`. -/
theorem lemma_4_14_expansion {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P₁ P₂ : Finpartition (Finset.univ : Finset V)) (U : Finset V) (hU : U ∈ P₂.parts)
    (hodd : IsOddCircuitSet G U)
    (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    (M₂ : Finset (ShrinkE G P₂)) (hM₂ : IsMatching (shrink G P₂) M₂) :
    (∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
      (∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
      ∃ M₁ : Finset (ShrinkE G P₁), IsMatching (shrink G P₁) M₁ ∧
        M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _)) ∧
    ((∀ e ∈ M₂, (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∉ (shrink G P₂).ends e) →
      ∀ u ∈ U, ∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
        (∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
        ∃ M₁ : Finset (ShrinkE G P₁), IsMatching (shrink G P₁) M₁ ∧
          M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _)) := by sorry

end PathsTreesFlowers.Invariance
