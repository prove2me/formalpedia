-- Prove2me | Theorems.Thm_Sendov_defect
-- name    : Sendov.defect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:41.217138+00:00
-- url     : https://prove2.me/theorems/1d57497f-1f9f-4756-b504-5e0c4a394b52
-- title:
--   Sendov: defect
-- statement:
--   **The defect lemma.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Defect.lean#L93-L121
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Defect.lean#L93-L121

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Defect
set_option autoImplicit false
open Sendov
open Multiset

theorem Sendov.defect : ∀ (s : Multiset ℂ), (∀ z ∈ s, ‖z‖ ≤ 1) →
    (s.map (fun z => ‖z‖)).prod * (s.map (fun z => ‖z⁻¹ - (starRingEnd ℂ) z‖)).sum
      ≤ 1 - ((s.map (fun z => ‖z‖)).prod) ^ 2 := by sorry
