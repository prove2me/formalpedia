-- Prove2me | Theorems.Thm_QEC_Coding_dual_middleCycleCode_carrier_eq_middleCocycleCode
-- name    : QEC.Coding.dual_middleCycleCode_carrier_eq_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:37:58.159394+00:00
-- url     : https://prove2.me/theorems/96e1470f-fc94-4a24-9990-408f3ce35cc0
-- title:
--   Coding: dual middle Cycle Code carrier eq middle Cocycle Code
-- statement:
--   The Coding construction uses the dual middle Cycle Code carrier eq middle Cocycle Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L104-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L104-L108

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.dual_middleCycleCode_carrier_eq_middleCocycleCode
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).middleCycleCode.carrier =
      K.middleCocycleCode.carrier := by sorry
