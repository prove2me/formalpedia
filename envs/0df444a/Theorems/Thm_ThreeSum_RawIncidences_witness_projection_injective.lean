-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_witness_projection_injective
-- name    : ThreeSum.RawIncidences.witness_projection_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:08.68611+00:00
-- url     : https://prove2.me/theorems/59d89fc4-9543-4123-8d8a-7dee0db2b716
-- title:
--   Raw Incidences: witness projection injective
-- statement:
--   Projection to the retained list is injective on the raw witnesses of
--   one original triple: the guard makes its lift unique.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L194-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/RawIncidences.lean#L194-L206

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds

theorem ThreeSum.RawIncidences.witness_projection_injective {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    Set.InjOn (fun w : Witness h J => List.ofFn w.1) (witnesses h J P d a b c) := by sorry
