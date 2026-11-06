-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
-- name    : QEC.Coding.ClassicalWeightReduction.boundary_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:21.839009+00:00
-- url     : https://prove2.me/theorems/b86c17b7-fbde-44d1-b05f-8bcc3087eb73
-- title:
--   Classical Weight Reduction: boundary single
-- statement:
--   The Classical Weight Reduction construction uses the boundary single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L522-L524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L522-L524

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

theorem QEC.Coding.ClassicalWeightReduction.boundary_single (i : WeightReducedBit R) :
    boundary (F := F) R (Pi.single i 1) = basisBoundary (F := F) R i := by sorry
