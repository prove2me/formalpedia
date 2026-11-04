-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRelations_span_mem_possibleSpans
-- name    : ThreeSum.TernaryCoverRelations.span_mem_possibleSpans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:05.501246+00:00
-- url     : https://prove2.me/theorems/aa989a68-817f-4ca5-8785-9acd8a6156cc
-- title:
--   Ternary Cover Relations: span mem possible Spans
-- statement:
--   Every actual trinary-column span appears in the finite list above.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L45-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L45-L87

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]

theorem ThreeSum.TernaryCoverRelations.span_mem_possibleSpans {d : ℕ} {σ : Type*} (columns : σ → Fin d → Fin 3) :
    Submodule.span K (Set.range fun j => digitVector (K := K) (columns j)) ∈
      possibleSpans K d := by sorry
