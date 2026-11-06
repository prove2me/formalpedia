-- Prove2me | Theorems.Thm_QEC_Coding_middleCohomologyDistanceAtLeast_dual_iff
-- name    : QEC.Coding.middleCohomologyDistanceAtLeast_dual_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:25.699833+00:00
-- url     : https://prove2.me/theorems/ca5bed5c-b1ab-46a5-b5dc-5df1c8587320
-- title:
--   Coding: middle Cohomology Distance At Least dual iff
-- statement:
--   Cohomological distance of the dual is homological distance of the
--   original complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L146-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Duality.lean#L146-L154

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem QEC.Coding.middleCohomologyDistanceAtLeast_dual_iff
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) :
    MiddleCohomologyDistanceAtLeast (dualChainComplex K) d ↔
      MiddleHomologyDistanceAtLeast K d := by sorry
