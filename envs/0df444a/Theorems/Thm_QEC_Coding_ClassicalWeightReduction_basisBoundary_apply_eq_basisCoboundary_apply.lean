-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_basisBoundary_apply_eq_basisCoboundary_apply
-- name    : QEC.Coding.ClassicalWeightReduction.basisBoundary_apply_eq_basisCoboundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:21.109326+00:00
-- url     : https://prove2.me/theorems/02c2e28a-e27e-49ea-8d72-01fbda896ea7
-- title:
--   Classical Weight Reduction: basis Boundary apply eq basis Coboundary apply
-- statement:
--   The explicitly described boundary and coboundary basis images are entries
--   of the same Tanner matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L529-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L529-L594

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
omit [Fintype F] [DecidableEq F]

theorem QEC.Coding.ClassicalWeightReduction.basisBoundary_apply_eq_basisCoboundary_apply
    (i : WeightReducedBit R) (q : WeightReducedCheck R) :
    basisBoundary (F := F) R i q = basisCoboundary (F := F) R q i := by sorry
