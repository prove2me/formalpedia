-- Prove2me | Theorems.Thm_Verification_IntervalContracts_every_checked_row_is_sound
-- name    : Verification.IntervalContracts.every_checked_row_is_sound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:20:26.211251+00:00
-- url     : https://prove2.me/theorems/3ee8a4a4-77d3-4d69-a175-d2054d92557e
-- title:
--   Soundness of a reusable interval contract table
-- statement:
--   Let a deterministic state transition and a family of state predicates be given. Each row of a finite table claims that every state satisfying its precondition reaches a state satisfying its postcondition after exactly the stated number of iterations. Rows may refer to earlier rows for sequential composition, repeated application of a common invariant, consequence, and cases. Identity and single-step rows have their direct local obligations. Any registered primitive must have its own soundness proof. If every row's local obligations hold on every state, every row's claimed interval contract holds.
-- source:
--   The program-proof rules are based on Hoare, An axiomatic basis for computer programming, Communications of the ACM 12(10), 1969, https://doi.org/10.1145/363235.363259. The present statement treats repeated references and exact integer durations in one table.

import Definitions.Def_ReusableIntervalContracts

open Verification.IntervalContracts

theorem Verification.IntervalContracts.every_checked_row_is_sound {S : Type*} (model : Model S) (code : Table)
    (checked : Checked model code) (i : ℕ) (present : i < code.length) :
    Holds model.step model.pred (out code i) := by sorry
