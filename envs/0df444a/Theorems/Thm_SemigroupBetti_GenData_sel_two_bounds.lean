-- Prove2me | Theorems.Thm_SemigroupBetti_GenData_sel_two_bounds
-- name    : SemigroupBetti.GenData.sel_two_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:55.193731+00:00
-- url     : https://prove2.me/theorems/dd7e34f2-ed6b-5e0f-9b42-e32361c579ea
-- title:
--   Gen Data: sel two bounds
-- statement:
--   **Lemma 9 (coordinate 2).** At a degree splitting along a pair `K ∋ 2`, the selected
--   `K`-vector has `1 ≤ v ≤ W - A - 1` at coordinate `2`.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L148-L166
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Identities.lean#L148-L166

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

theorem SemigroupBetti.GenData.sel_two_bounds {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    (h2 : 2 ∈ K) : 1 ≤ G.sel d K 2 ∧ G.sel d K 2 ≤ G.W - G.A - 1 := by sorry
