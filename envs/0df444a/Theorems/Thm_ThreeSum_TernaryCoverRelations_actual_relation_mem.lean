-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRelations_actual_relation_mem
-- name    : ThreeSum.TernaryCoverRelations.actual_relation_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:19.218253+00:00
-- url     : https://prove2.me/theorems/ceec2e94-5782-4473-bb78-c280c32a9625
-- title:
--   Ternary Cover Relations: actual relation mem
-- statement:
--   The Ternary Cover Relations construction uses the actual relation mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L129-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L129-L133

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

theorem ThreeSum.TernaryCoverRelations.actual_relation_mem {d : ℕ} {σ : Type*} (columns : σ → Fin d → Fin 3) :
    relationSpace (Submodule.span K (Set.range fun j => digitVector (K := K) (columns j))) ∈
      possibleRelations K d := by sorry
