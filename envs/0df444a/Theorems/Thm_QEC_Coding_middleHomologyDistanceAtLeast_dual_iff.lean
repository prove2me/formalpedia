-- Prove2me | Theorems.Thm_QEC_Coding_middleHomologyDistanceAtLeast_dual_iff
-- name    : QEC.Coding.middleHomologyDistanceAtLeast_dual_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:03:43.384888+00:00
-- url     : https://prove2.me/theorems/cb9d52a8-ea80-4899-9b55-f8271a69ed35
-- title:
--   Coding: middle Homology Distance At Least dual iff
-- statement:
--   Homological distance of the dual is exactly cohomological distance of the
--   original complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L127-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L127-L133

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.middleHomologyDistanceAtLeast_dual_iff
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) :
    MiddleHomologyDistanceAtLeast (dualChainComplex K) d ↔
      MiddleCohomologyDistanceAtLeast K d := by sorry
