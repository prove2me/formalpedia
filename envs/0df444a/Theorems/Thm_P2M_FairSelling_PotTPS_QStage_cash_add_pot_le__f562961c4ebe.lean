-- Prove2me | Theorems.Thm_P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe
-- name    : P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:18.444062+00:00
-- url     : https://prove2.me/theorems/cbb49d67-3d15-485d-b7e3-8e2def65edb9
-- title:
--   P2 M Fair Selling Pot TPS QStage cash add pot le  f562961c4ebe: P2 M Fair Selling Pot TPS QStage cash add pot le  f562961c4ebe
-- statement:
--   The slice an agent holds, together with the pot of its good, does not exceed the price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L266-L272
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L266-L272

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
omit [Fintype G]

theorem P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe {s : QStage G n} (hcn : ∀ i, 0 ≤ s.cash i) {i : Fin n} {g : G}
    (hg : g ∈ s.src i) : s.cash i + s.pot p g ≤ p g := by sorry

alias «FairSelling».«PotTPS».«QStage».«cash_add_pot_le'» := P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe
