-- Prove2me | Theorems.Thm_PathsTreesFlowers_Duality_Supplement_extension_4_7
-- name    : PathsTreesFlowers.Duality.Supplement.extension_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:40:54.828931+00:00
-- url     : https://prove2.me/theorems/19279894-6dbf-4861-a1eb-021b1a10c489
-- title:
--   4.7 — Any exposed vertex is a planted tree; every planted tree extends to an augmenting, flowered or Hungarian tree, inspecting each relevant edge at most once
-- statement:
--   Fix a matching $M$ in a finite loopless multigraph $G$. Every exposed vertex $r$ gives the singleton planted tree. Every planted tree $J$ rooted at $r$ has a finite run of the five-case search of 4.7, starting with no discarded edges and ending with an augmenting, flowered or Hungarian tree. The old inner vertices, outer vertices, edges and root are preserved.
--
--   If $L$ is the concatenated list of inspected edge identities, including the final stopping edge when present, then
--   $$\forall e\in E(G),\quad\operatorname{count}_L(e)\le1.$$
--
--   The list has no repetitions and every inspected edge has both endpoints in the actual terminal object's vertex set. Every intermediate search state satisfies the planted-tree and discarded-edge invariants. Growing the tree records both the inspected extension edge and the newly retrieved matching edge. This retains the source's finite, constant-1 guarantee, including zero continuing steps.
--
--   Differences from the source:
--   - encoding: extend a planted tree by the five cases in the proof → a finite SearchRun followed by SearchStop, with ValidState at intermediate states and the separate terminal trichotomy; reason: the continuing rules are exactly cases (2) and (5); stopping rules are cases (1), (3) and (4), and do not assume their output properties
--   - encoding: looking at most once at each relevant edge → a list of actual inspected edge identities, no repetitions, count at most 1, with both endpoints in the final vertex set; reason: this expresses the parenthetical as an exact finite count; the matching edge retrieved in case (5) is also recorded
-- source:
--   Edmonds, Paths, trees, and flowers, Canad. J. Math. 17 (1965), p. 456, 4.7

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees

namespace PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem extension_4_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) :
    (∀ r, IsExposed G M r → IsPlantedTree G M (singletonTree G r) r) ∧
    ∀ (J : AltTree G) (r : V), IsPlantedTree G M J r →
      ∃ (S : SearchState G) (log tail : List E) (U : Finset V),
        SearchRun G M ⟨J, ∅⟩ log S ∧ SearchStop G M S tail U ∧
        ValidState G M r S ∧ TerminalTree G M r S tail U ∧
        J.inner ⊆ S.tree.inner ∧ J.outer ⊆ S.tree.outer ∧ J.edges ⊆ S.tree.edges ∧
        (log ++ tail).Nodup ∧ (∀ e : E, (log ++ tail).count e ≤ 1) ∧
        (∀ e ∈ log ++ tail, G.ends e ∈ U.sym2) ∧
        (∀ (T : SearchState G) (a b : List E),
          SearchRun G M ⟨J, ∅⟩ a T → SearchRun G M T b S → log = a ++ b →
          ValidState G M r T) := by sorry

end PathsTreesFlowers.Duality.Supplement
