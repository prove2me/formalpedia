-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_no_replace
-- name    : SemigroupBetti.GenData.no_replace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:54:23.817237+00:00
-- url     : https://prove2.me/theorems/06332460-9337-567b-8355-daf6304ae261
-- title:
--   Gen Data: no replace
-- statement:
--   **Selected-vector replacement principle** (Lemma 2 applied to the selected vectors): at a
--   degree splitting along a pair `K`, no replacement `z - U + V` of the selected `K`-vector `z`
--   keeps a coordinate of `z` and gains a coordinate outside `K`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L233-L243
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Partition.lean#L233-L243

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.no_replace {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    {U V : Fin 4 → ℕ} (hUz : U ≤ G.sel d K) (hUV : G.nu U = G.nu V) {k j : Fin 4}
    (hk : U k < G.sel d K k) (hj : j ∉ K) (hVj : 0 < V j) : False := by sorry
