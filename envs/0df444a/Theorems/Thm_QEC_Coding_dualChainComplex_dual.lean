-- Prove2me | Theorems.Thm_QEC_Coding_dualChainComplex_dual
-- name    : QEC.Coding.dualChainComplex_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:53.110107+00:00
-- url     : https://prove2.me/theorems/5286bd99-67c7-4401-a94a-8ee4ba139d1f
-- title:
--   Coding: dual Chain Complex dual
-- statement:
--   Dualization is involutive at the level of boundary maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L136-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L136-L142

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.dualChainComplex_dual
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    dualChainComplex (dualChainComplex K) = K := by sorry
