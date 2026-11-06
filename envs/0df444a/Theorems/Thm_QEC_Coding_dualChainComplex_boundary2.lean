-- Prove2me | Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
-- name    : QEC.Coding.dualChainComplex_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:37.3708+00:00
-- url     : https://prove2.me/theorems/f5f0e258-cdbf-4c0d-9352-05c079bb8406
-- title:
--   Coding: dual Chain Complex boundary2
-- statement:
--   The Coding construction uses the dual Chain Complex boundary2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L98-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L98-L102

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.dualChainComplex_boundary2
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).boundary2 =
      wordLinearMapTranspose K.boundary1 := by sorry

attribute [defeq] QEC.Coding.dualChainComplex_boundary2
