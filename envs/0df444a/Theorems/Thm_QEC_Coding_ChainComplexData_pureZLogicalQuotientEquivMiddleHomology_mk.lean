-- Prove2me | Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
-- name    : QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:53.923142+00:00
-- url     : https://prove2.me/theorems/5abaec0f-baf3-46c4-bb94-1a79fe8f03f1
-- title:
--   Chain Complex Data: pure ZLogical Quotient Equiv Middle Homology mk
-- statement:
--   The Chain Complex Data construction uses the pure ZLogical Quotient Equiv Middle Homology mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L997-L1003
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L997-L1003

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
open QEC.Coding.ChainComplexData
variable {F : Type u} {ι : Type v} {C0 C2 : Type (max u v)} [Field F] [Fintype F]
    [Fintype ι] [AddCommGroup C0] [Module F C0] [AddCommGroup C2] [Module F C2]

theorem QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk {κ lambda : Type v}
    [Fintype κ] [Fintype lambda]
    (K : ChainComplexData F (Word F κ) (Word F ι) (Word F lambda))
    (x : K.firstCoboundaryCheckCode.dual.carrier) :
    K.pureZLogicalQuotientEquivMiddleHomology (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.firstCoboundaryDualEquivMiddleCycleCode x) := by sorry

attribute [defeq] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
