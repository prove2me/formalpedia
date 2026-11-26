-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_le_of_coords
-- name    : SemigroupBetti.GenData.sel_le_of_coords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:39.056678+00:00
-- url     : https://prove2.me/theorems/74913533-81a5-44ea-9aa8-82c6835560ee
-- title:
--   Gen Data: sel le of coords
-- statement:
--   Two selected `K`-vectors (`K = {i,k}`) are comparable iff their `i`- and `k`-coordinates are.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L29-L39
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean#L29-L39

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.sel_le_of_coords {K : Finset (Fin 4)} {i k : Fin 4} (hKe : K = {i, k}) (hK : K.card = 2)
    {d d' : ℕ} (hS : G.IsSplit d K) (hS' : G.IsSplit d' K)
    (hi : G.sel d K i ≤ G.sel d' K i) (hk : G.sel d K k ≤ G.sel d' K k) :
    G.sel d K ≤ G.sel d' K := by sorry
