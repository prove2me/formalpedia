-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_finrank_ker_reducedBoundary
-- name    : QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.finrank_ker_reducedBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:10.610556+00:00
-- url     : https://prove2.me/theorems/28a9f61c-9494-474b-b7dd-8fde978f2826
-- title:
--   Classical Row Reduction: finrank ker reduced Boundary
-- statement:
--   The Classical Row Reduction construction uses the finrank ker reduced Boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L155-L159

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20 QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]

theorem QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.finrank_ker_reducedBoundary
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Module.finrank (ZMod 2) (LinearMap.ker (reducedBoundary Y)) =
      Module.finrank (ZMod 2) (LinearMap.ker Y) := by sorry
