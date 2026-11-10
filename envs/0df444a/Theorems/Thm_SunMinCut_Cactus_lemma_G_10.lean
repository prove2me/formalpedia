-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_G_10
-- name    : SunMinCut.Cactus.lemma_G_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:04.813129+00:00
-- url     : https://prove2.me/theorems/52bec40d-20a1-462c-aa4a-7ff2ac49e973
-- title:
--   Lemma G.10 — unique global minimal shores
-- statement:
--   Let $G$ be a connected aggregated graph on $n\ge2$ vertices with positive capacities and root $r$. An object is a vertex $\{v\}$ or the endpoint set of a record; a feasible minimum shore for $Z$ is a minimum-cut shore avoiding $r$ and containing $Z$. Let $(K_j,\pi_j)$, $j<L$, be cacti with surjective $\pi_j$; the local answer of $K_j$ for $Z$ is the smallest represented root-avoiding shore of value $\lambda$ containing $Z$, or absent if there is none.
--   1. Every existing required shore is unique and contained in every feasible minimum shore for that object.
--   2. On the cover event (every minimum cut is represented by some $K_j$): for any local answers, an existing local answer of minimum original cardinality is the required shore.
--   3. On the cover event, missing local answers everywhere are equivalent to a missing global answer.
--
--   Differences from the source:
--   - encoding: local answers of the cacti filtered at the computed value λ̂ → local answers at λ, given as any family satisfying the local-answer specification; reason: on the cover event λ̂ = λ, the case in which the paper proves the lemma (App. G.3)
--   - generalization: the retained auxiliary cacti on the cover event → any finite family of cacti with surjective bag maps satisfying the cover condition; reason: all retained auxiliary cacti satisfy these conditions, and the inclusion and minimum-cardinality assertions require only coverage, not their sampling history
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma G.10, p. 49

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Intervals

namespace SunMinCut.Cactus

/-- **Lemma G.10 (Unique global minimal shores)**, Sun 2026, doi:10.5281/zenodo.23915020, p. 49.
Objects are vertices `{v}` and the endpoint sets of records; a feasible minimum shore for `Z`
is a minimum-cut shore avoiding the root `r` and containing `Z`. (1) Every existing required
shore is unique and contained in every feasible minimum shore for that object. Given cacti
`(K_j, π_j)` (with surjective `π_j`), whose local answer for `Z` is the smallest represented
root-avoiding shore of value `λ` containing `Z`, or absent: on the cover event (every minimum cut
is represented by some `K_j`), (2) minimum original cardinality among the local answers selects
the required shore, and (3) missing local answers everywhere are equivalent to a missing global
answer. -/
theorem lemma_G_10 (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (hagg : Aggregated G) (r : Fin n) (L : ℕ) (qs es : Fin L → ℕ)
    (K : ∀ j, MGraph (qs j) (es j)) (π : ∀ j, Fin n → Fin (qs j))
    (hK : ∀ j, (K j).IsCactus ∧ Function.Surjective (π j)) :
    (∀ Z, IsObject G Z → (feasible {S | IsMinCut G S} r Z).Nonempty →
      ∃! S, IsLeast' (feasible {S | IsMinCut G S} r Z) S) ∧
    ((∀ S, IsMinCut G S → ∃ j, bip S ∈ repCuts (K j) (π j)) →
      (∀ Z, IsObject G Z → ∀ A : Fin L → Option (Finset (Fin n)),
        (∀ j, (A j = none ↔
            feasible {S | bip S ∈ repCuts (K j) (π j) ∧ cutw G S = lam G} r Z = ∅) ∧
          ∀ S, A j = some S →
            IsLeast' (feasible {S | bip S ∈ repCuts (K j) (π j) ∧ cutw G S = lam G} r Z) S) →
        ∀ j S, A j = some S → (∀ i S', A i = some S' → S.card ≤ S'.card) →
          IsLeast' (feasible {S | IsMinCut G S} r Z) S) ∧
      ∀ Z, IsObject G Z →
        ((∀ j, feasible {S | bip S ∈ repCuts (K j) (π j) ∧ cutw G S = lam G} r Z = ∅) ↔
          feasible {S | IsMinCut G S} r Z = ∅)) := by sorry

end SunMinCut.Cactus
