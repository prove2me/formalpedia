-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
-- name    : QEC.Coding.ClassicalWeightReduction.originalBoundary_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:29.409486+00:00
-- url     : https://prove2.me/theorems/19cad929-89c1-4a89-b66a-a2b76ca0f293
-- title:
--   Classical Weight Reduction: original Boundary single
-- statement:
--   The Classical Weight Reduction construction uses the original Boundary single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L506-L509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L506-L509

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

theorem QEC.Coding.ClassicalWeightReduction.originalBoundary_single (b : Bit) :
    originalBoundary (F := F) R (Pi.single b 1) =
      originalBasisBoundary (F := F) R b := by sorry
