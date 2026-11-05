-- Prove2me | Theorems.Thm_TenChallenges_ryser_common_vertex
-- name    : TenChallenges.ryser_common_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:37.211188+00:00
-- url     : https://prove2.me/theorems/fd3aca2e-3563-4c01-b6cf-d2099bc3bc4e
-- title:
--   Ryser conjecture: All edges have a common vertex
-- statement:
--   Let r≥2 and let H be a finite hypergraph with a vertex belonging to every edge. Then H satisfies Ryser’s inequality whenever it is r-uniform and r-partite.
-- source:
--   Elementary special case / supporting lemma for Challenge 08. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_TenChallenges_Challenge_08

theorem TenChallenges.ryser_common_vertex {V : Type*} [DecidableEq V] (H : FinHypergraph V)
    (r : ℕ) (hr : 2 ≤ r) (v : V) (hv : v ∈ H.vertices)
    (hcommon : ∀ e ∈ H.edges, v ∈ e) : H.RyserConjectureFor r := by sorry
