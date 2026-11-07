-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_ClassicalRowReduction_reducedBoundary_rowWeight
-- name    : QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_rowWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:48.635237+00:00
-- url     : https://prove2.me/theorems/86c89e0e-a16a-4277-a9fb-5949a0c67e7c
-- title:
--   Classical Row Reduction: reduced Boundary row Weight
-- statement:
--   Every selected row is literally an original row, so row weight does not
--   increase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L177-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean#L177-L201

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

theorem QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction.reducedBoundary_rowWeight
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    {w : Nat}
    (hRow : ∀ b, HammingWeight
      (wordLinearMapTranspose Y (Pi.single b 1)) ≤ w) :
    ∀ r, HammingWeight
      (wordLinearMapTranspose (reducedBoundary Y) (Pi.single r 1)) ≤ w := by sorry
