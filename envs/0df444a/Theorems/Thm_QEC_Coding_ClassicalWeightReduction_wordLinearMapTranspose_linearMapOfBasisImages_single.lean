-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_wordLinearMapTranspose_linearMapOfBasisImages_single
-- name    : QEC.Coding.ClassicalWeightReduction.wordLinearMapTranspose_linearMapOfBasisImages_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:47.931885+00:00
-- url     : https://prove2.me/theorems/55341731-22b9-4426-8915-1b7b2d2cb02d
-- title:
--   Classical Weight Reduction: word Linear Map Transpose linear Map Of Basis Images single
-- statement:
--   Transposing a basis-image linear map exposes one matrix row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L483-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L483-L502

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

theorem QEC.Coding.ClassicalWeightReduction.wordLinearMapTranspose_linearMapOfBasisImages_single
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) (q : Target) :
    wordLinearMapTranspose (linearMapOfBasisImages (F := F) image)
        (Pi.single q 1) = fun i => image i q := by sorry
