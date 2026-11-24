-- Prove2me | Theorems.Thm_P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb
-- name    : P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:25.541089+00:00
-- url     : https://prove2.me/theorems/e44b3ff2-c25c-4285-963e-08d0690b077a
-- title:
--   P2 M Fair Selling MMS2 cash of one good loss  47c1f0f02fdb: P2 M Fair Selling MMS2 cash of one good loss  47c1f0f02fdb
-- statement:
--   Removing a single good, written with the `K ∪ S` shape used by the composition lemma.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L158-L164
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L158-L164

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (K S : Finset G) (e : G) (hKS : K ∪ S = {e}) (c m : ℝ) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hmτ : m ≤ (3 / 4 : ℝ) * MMS 3 w p) (hme : m ≤ p e) (hcm : p e ≤ c + m) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
      (cashPrice (Finset.univ \ (K ∪ S)) p c) := by sorry

alias «FairSelling».«MMS2_cash_of_one_good_loss'» := P2M_FairSelling_MMS2_cash_of_one_good_loss__47c1f0f02fdb
