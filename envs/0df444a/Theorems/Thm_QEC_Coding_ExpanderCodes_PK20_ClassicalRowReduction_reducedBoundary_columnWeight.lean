-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_reducedBoundary_columnWeight
-- name    : QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_columnWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:41.346204+00:00
-- url     : https://prove2.me/theorems/45d21845-8ac9-4ae8-8d48-b77f86cfd827
-- title:
--   Classical Row Reduction: reduced Boundary column Weight
-- statement:
--   Deleting rows also cannot increase a column weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L229-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L229-L259

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

theorem QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_columnWeight
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (a : bit) :
    HammingWeight (reducedBoundary Y (Pi.single a 1)) ≤
      HammingWeight (Y (Pi.single a 1)) := by sorry
