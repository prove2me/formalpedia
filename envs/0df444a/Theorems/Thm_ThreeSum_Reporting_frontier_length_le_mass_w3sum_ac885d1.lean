-- Prove2me | Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass_w3sum_ac885d1
-- name    : ThreeSum.Reporting.frontier_length_le_mass_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:39.061223+00:00
-- url     : https://prove2.me/theorems/6d7315c6-2f1e-4020-afb1-a4458edb145c
-- title:
--   Reporting: frontier length le mass
-- statement:
--   The list is precisely the positive fibers, so its size is bounded by
--   the root mass, even if different raw incidences have the same value.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean#L128-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean#L128-L152

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting
set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]

theorem ThreeSum.Reporting.frontier_length_le_mass_w3sum_ac885d1 (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hc : ∀ k, (children k).Nodup) (hk : k ≤ J) :
    (frontier children query k).length ≤ ∑ i ∈ I, weight i := by sorry
