-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_card_reducedCheck_le
-- name    : QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.card_reducedCheck_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:23:39.334099+00:00
-- url     : https://prove2.me/theorems/1cf78b36-cb32-47bb-ba58-36e906c3a94e
-- title:
--   Classical Row Reduction: card reduced Check le
-- statement:
--   Row reduction never creates more checks than the original matrix had.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L222-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L222-L226

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

theorem QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.card_reducedCheck_le
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Fintype.card (ReducedCheck Y) ≤ Fintype.card check := by sorry
