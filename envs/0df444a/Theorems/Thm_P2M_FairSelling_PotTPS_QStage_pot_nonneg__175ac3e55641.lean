-- Prove2me | Theorems.Thm_P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641
-- name    : P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:52.158801+00:00
-- url     : https://prove2.me/theorems/1082f4fe-9870-4c6b-b8cc-f848711bbc89
-- title:
--   P2 M Fair Selling Pot TPS QStage pot nonneg  175ac3e55641: P2 M Fair Selling Pot TPS QStage pot nonneg  175ac3e55641
-- statement:
--   The P2 M Fair Selling Pot TPS QStage pot nonneg  175ac3e55641 construction uses the P2 M Fair Selling Pot TPS QStage pot nonneg  175ac3e55641 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L329-L338
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L329-L338

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

theorem P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641 (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps) (g : G) :
    0 ≤ s.pot p g := by sorry

alias «FairSelling».«PotTPS».«QStage».«pot_nonneg'» := P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641
