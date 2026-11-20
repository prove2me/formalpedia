-- Prove2me | Theorems.Thm_Petersen_exists_isPerfectMatching_of_bridgeless_cubic
-- name    : Petersen.exists_isPerfectMatching_of_bridgeless_cubic
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:13.633974+00:00
-- url     : https://prove2.me/theorems/f604c3e2-bedf-4af8-adac-078975ea5e9b
-- title:
--   Petersen's Theorem (1891): Every Finite Bridgeless Cubic Graph Has a Perfect Matching
-- statement:
--   **Petersen's Theorem (1891).** Every finite bridgeless $3$-regular (cubic) simple graph $G$ admits a perfect matching.
-- source:
--   Julius Petersen, Die Theorie der regulären graphs, Acta Mathematica 15 (1891), 193–220.

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Tutte

universe u
namespace Petersen

theorem exists_isPerfectMatching_of_bridgeless_cubic
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcubic : ∀ v : V, (G.neighborSet v).encard = 3)
    (hbridgeless : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by sorry
end Petersen
