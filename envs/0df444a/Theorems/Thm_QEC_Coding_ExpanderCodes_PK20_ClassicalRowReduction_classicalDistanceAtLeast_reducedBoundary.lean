-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_classicalDistanceAtLeast_reducedBoundary
-- name    : QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.classicalDistanceAtLeast_reducedBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:16.841912+00:00
-- url     : https://prove2.me/theorems/33cab1e0-66d6-4e7a-be7c-1677cd691bbd
-- title:
--   Classical Row Reduction: classical Distance At Least reduced Boundary
-- statement:
--   The Classical Row Reduction construction uses the classical Distance At Least reduced Boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L161-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L161-L173

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

theorem QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.classicalDistanceAtLeast_reducedBoundary
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {d : Nat}
    (hDistance : ClassicalDistanceAtLeast (LinearMap.toMatrix' Y) d) :
    ClassicalDistanceAtLeast
      (LinearMap.toMatrix' (reducedBoundary Y)) d := by sorry
