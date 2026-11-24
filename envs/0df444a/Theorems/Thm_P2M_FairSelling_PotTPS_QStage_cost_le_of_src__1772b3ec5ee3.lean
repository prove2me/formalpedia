-- Prove2me | Theorems.Thm_P2M_FairSelling_PotTPS_QStage_cost_le_of_src__1772b3ec5ee3
-- name    : P2M_FairSelling_PotTPS_QStage_cost_le_of_src__1772b3ec5ee3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:14.372443+00:00
-- url     : https://prove2.me/theorems/76177b6f-2d48-40e0-9483-f8cdc87d8e04
-- title:
--   P2 M Fair Selling Pot TPS QStage cost le of src  1772b3ec5ee3: P2 M Fair Selling Pot TPS QStage cost le of src  1772b3ec5ee3
-- statement:
--   **The cost of a slice holder**, from the local data only.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L279-L289
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L279-L289

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem P2M_FairSelling_PotTPS_QStage_cost_le_of_src__1772b3ec5ee3 (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} {i : Fin n} {g : G}
    (hb : s.bundle i = ∅) (ho : s.own i = ∅) (hrz : s.resv i = 0) (hsrc : s.src i = {g})
    (hle : s.cash i + s.pot p g ≤ p g) {j : Fin n}
    (hcash : s.cash i ≤ GeneralTPS.thr v p j) :
    s.cost v p i j ≤ 2 * GeneralTPS.thr v p j := by sorry

alias «FairSelling».«PotTPS».«QStage».«cost_le_of_src'» := P2M_FairSelling_PotTPS_QStage_cost_le_of_src__1772b3ec5ee3
