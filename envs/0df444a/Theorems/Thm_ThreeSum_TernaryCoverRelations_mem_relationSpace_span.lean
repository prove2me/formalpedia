-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRelations_mem_relationSpace_span
-- name    : ThreeSum.TernaryCoverRelations.mem_relationSpace_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:16.685203+00:00
-- url     : https://prove2.me/theorems/c07ffbc9-a3c7-44da-adf2-92fd5754a3a0
-- title:
--   Ternary Cover Relations: mem relation Space span
-- statement:
--   The Ternary Cover Relations construction uses the mem relation Space span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L101-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean#L101-L118

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

theorem ThreeSum.TernaryCoverRelations.mem_relationSpace_span {d : ℕ} {σ : Type*}
    (columns : σ → Fin d → Fin 3) (a : Fin d → K) :
    a ∈ relationSpace (Submodule.span K (Set.range fun j => digitVector (K := K) (columns j))) ↔
      ∀ j : σ, ∑ i, a i * digitVector (K := K) (columns j) i = 0 := by sorry
