-- Prove2me | Theorems.Thm_QEC_Coding_dual_middleBoundaryCode_carrier_eq_firstCoboundaryCheckCode
-- name    : QEC.Coding.dual_middleBoundaryCode_carrier_eq_firstCoboundaryCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:24.662759+00:00
-- url     : https://prove2.me/theorems/41fcce79-9807-407e-afbd-5e0746fc5ca7
-- title:
--   Coding: dual middle Boundary Code carrier eq first Coboundary Check Code
-- statement:
--   The Coding construction uses the dual middle Boundary Code carrier eq first Coboundary Check Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L110-L114

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.dual_middleBoundaryCode_carrier_eq_firstCoboundaryCheckCode
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).middleBoundaryCode.carrier =
      K.firstCoboundaryCheckCode.carrier := by sorry
