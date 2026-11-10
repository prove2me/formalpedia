-- Prove2me | Theorems.Thm_SunMinCut_Cactus_capforest_36
-- name    : SunMinCut.Cactus.capforest_36
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:24:24.71249+00:00
-- url     : https://prove2.me/theorems/cd3d62ce-18dc-4634-b6ae-fc64d3592e63
-- title:
--   App. B.1 (36) — the CAPFOREST certificate of Nagamochi and Ibaraki
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices with positive capacities and let $\sigma$ be a maximum-adjacency ordering of its vertices (each selected vertex has the largest total capacity to the already selected vertices; the published `IsLegalOrdering`). Scan the records at each selected vertex in index order; when a non-loop record $e$ increases the label of its later endpoint, let $q_e$ be that label after the increase. Then
--   $$q_e\le w(C)$$
--   for every cut $C$ (shore $S$) separating the endpoints of $e$.
--
--   Differences from the source:
--   - encoding: edges scanned in an unspecified order when a vertex is selected → records at a selected vertex scanned in index order; reason: G ranges over all record numberings, so every scan order is covered
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, App. B.1, equation (36), p. 33

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph_IsLegalOrdering
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_Processes

namespace SunMinCut.Cactus

/-- **The CAPFOREST certificate (36)** of Nagamochi and Ibaraki, as used in Sun 2026,
doi:10.5281/zenodo.23915020, App. B.1, p. 33: in a maximum-adjacency ordering `σ` (a legal
ordering: each selected vertex has the largest capacity to the already selected vertices), let
`q_e` be the label of the later endpoint of the record `e` right after `e` increases it; then
`q_e ≤ w(C)` for every cut `C` separating the endpoints of `e`. -/
theorem capforest_36 (n m : ℕ) (hn : 2 ≤ n) (G : Graph n m) (hpos : Positive G)
    (hconn : Connected G) (σ : Fin n ≃ Fin n) (hσ : G.IsLegalOrdering σ) (e : Fin m)
    (he : ¬ (G.ends e).IsDiag) (S : Finset (Fin n))
    (hS : (∃ a ∈ G.ends e, a ∈ S) ∧ ∃ b ∈ G.ends e, b ∉ S) :
    capforestLabel G σ e ≤ cutw G S := by sorry

end SunMinCut.Cactus
