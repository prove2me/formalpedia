-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_ncomp_sub_one_le
-- name    : SemigroupBetti.GenData.ncomp_sub_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:56.120087+00:00
-- url     : https://prove2.me/theorems/54c5d373-bb4d-5fab-a113-faf808ee3fff
-- title:
--   Gen Data: ncomp sub one le
-- statement:
--   **Lemma 4, per-degree step.** For `d ∈ 𝓢`: `c_d - 1 ≤ r_d ≤ #{i : cᵢ nᵢ = d}`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L270-L318
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Critical.lean#L270-L318

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.ncomp_sub_one_le {d : ℕ} (hd : G.contributes d) (hS : G.HasSingletonComp d) :
    G.ncomp d - 1 ≤ (G.critIndices d).card := by sorry
