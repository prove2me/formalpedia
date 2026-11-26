-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_one_bounds
-- name    : SemigroupBetti.GenData.sel_one_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:19.059215+00:00
-- url     : https://prove2.me/theorems/cdec4958-bf8a-4a81-8211-fa07565673b9
-- title:
--   Gen Data: sel one bounds
-- statement:
--   **Lemma 9 (coordinate 1).** At a degree splitting along a pair `K ∋ 1`, the selected
--   `K`-vector has `1 ≤ u ≤ B - 1` at coordinate `1`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L126-L144
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L126-L144

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)

theorem SemigroupBetti.GenData.sel_one_bounds {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    (h1 : 1 ∈ K) : 1 ≤ G.sel d K 1 ∧ G.sel d K 1 ≤ G.B - 1 := by sorry
