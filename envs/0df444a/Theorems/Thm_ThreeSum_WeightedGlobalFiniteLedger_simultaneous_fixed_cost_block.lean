-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFiniteLedger_simultaneous_fixed_cost_block
-- name    : ThreeSum.WeightedGlobalFiniteLedger.simultaneous_fixed_cost_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:56.779771+00:00
-- url     : https://prove2.me/theorems/a947c435-dcdb-4005-bc32-50c512b94fd5
-- title:
--   Weighted Global Finite Ledger: simultaneous fixed cost block
-- statement:
--   The Weighted Global Finite Ledger construction uses the simultaneous fixed cost block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFiniteLedger.lean#L99-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFiniteLedger.lean#L99-L107

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology

theorem ThreeSum.WeightedGlobalFiniteLedger.simultaneous_fixed_cost_block (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) ∧
      0 < outputRate (scale C c' d) ∧ primeRate (scale C c' d) < outputRate (scale C c' d) := by sorry
