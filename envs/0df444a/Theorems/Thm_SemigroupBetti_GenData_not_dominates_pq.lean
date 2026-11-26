-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_not_dominates_pq
-- name    : SemigroupBetti.GenData.not_dominates_pq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:45.3508+00:00
-- url     : https://prove2.me/theorems/70dcc8a5-85a7-5a9b-9bb0-bed36206cd0f
-- title:
--   Gen Data: not dominates pq
-- statement:
--   **Lemma 12, exclusion step.** At a degree of `ℰ`, the selected interior vector `(0,u,v,0)`
--   does not satisfy `u ≥ p`, `v ≥ q`, `(u,v) ≠ (p,q)`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L201-L216
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean#L201-L216

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.not_dominates_pq {d : ℕ} (hd : d ∈ G.famE) (hu : G.p ≤ G.sel d {1, 2} 1)
    (hv : G.q ≤ G.sel d {1, 2} 2) (hne : (G.sel d {1, 2} 1, G.sel d {1, 2} 2) ≠ (G.p, G.q)) :
    False := by sorry
