-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedBudgetSelector_exists_budget_row
-- name    : ThreeSum.TernaryPairedBudgetSelector.exists_budget_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:38.257201+00:00
-- url     : https://prove2.me/theorems/8fa63ffc-68dd-4407-9481-e228bc6b3460
-- title:
--   Ternary Paired Budget Selector: exists budget row
-- statement:
--   Exact upper-budget selection. The initial paired potential is never
--   computed; only its proved integer upper bound U is used by the machine.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean#L11-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedBudgetSelector.lean#L11-L60

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem ThreeSum.TernaryPairedBudgetSelector.exists_budget_row {Ω : Type*} [DecidableEq Ω]
    (S : Finset Ω) (hS : S.Nonempty) (a c p s j U N curPi curB curC : ℕ)
    (ha : 0<a) (hp : 0<p) (nextPi nextB nextC : Ω→ℕ)
    (hPi : a*(∑ x∈S,nextPi x)≤3*S.card*c*curPi)
    (hB : p*(∑ x∈S,nextB x)≤3*S.card*curB)
    (hC : p*(∑ x∈S,nextC x)≤3*S.card*curC)
    (hPiBudget : a^j*curPi≤(9*c)^j*U)
    (hBBudget : p^j*curB≤9^j*N) (hCBudget : p^j*curC≤9^j*N) :
    ∃ x∈S,
      a^(j+1)*(s*nextPi x)≤s*(9*c)^(j+1)*U ∧
      p^(j+1)*nextB x≤9^(j+1)*N ∧ p^(j+1)*nextC x≤9^(j+1)*N := by sorry
