-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_boundary_single
-- name    : QEC.Coding.ClassicalWeightReduction.transpose_boundary_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:51.018049+00:00
-- url     : https://prove2.me/theorems/6d8f2be2-fb16-4b68-829d-e5190aed9416
-- title:
--   Classical Weight Reduction: transpose boundary single
-- statement:
--   Every named coboundary basis word is the corresponding row of the actual
--   weight-reduced boundary operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L599-L605
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L599-L605

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq F]

theorem QEC.Coding.ClassicalWeightReduction.transpose_boundary_single (q : WeightReducedCheck R) :
    wordLinearMapTranspose (boundary (F := F) R) (Pi.single q 1) =
      basisCoboundary (F := F) R q := by sorry
