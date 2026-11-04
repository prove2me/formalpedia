-- Prove2me | Theorems.Thm_ThreeSum_Reporting_mem_frontier_iff_w3sum_ac885d1
-- name    : ThreeSum.Reporting.mem_frontier_iff_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:36.844063+00:00
-- url     : https://prove2.me/theorems/f45521d3-e5c4-4a9f-9676-340f2122b3b9
-- title:
--   Reporting: mem frontier iff
-- statement:
--   The Reporting construction uses the mem frontier iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean#L61-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Reporting.lean#L61-L103

import Definitions.Def_Submission_ThreeSum_Subset
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Definitions.Def_Submission_ThreeSum_Reporting
set_option autoImplicit false
open ThreeSum ThreeSum.Reporting
open Finset
open scoped BigOperators
variable {ι α : Type*} [DecidableEq α]

theorem ThreeSum.Reporting.mem_frontier_iff_w3sum_ac885d1 (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hk : k ≤ J) (pre : List α) :
    pre ∈ frontier children query k ↔ 0 < mass I word weight k pre := by sorry
