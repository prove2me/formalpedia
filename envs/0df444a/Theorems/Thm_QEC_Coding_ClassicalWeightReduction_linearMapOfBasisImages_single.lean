-- Prove2me | Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
-- name    : QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:28.734219+00:00
-- url     : https://prove2.me/theorems/178d2e8c-1234-42e0-b55b-fb352e95c226
-- title:
--   Classical Weight Reduction: linear Map Of Basis Images single
-- statement:
--   The Classical Weight Reduction construction uses the linear Map Of Basis Images single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L464-L479
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean#L464-L479

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

theorem QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) (i : Source) :
    linearMapOfBasisImages (F := F) image (Pi.single i 1) = image i := by sorry
