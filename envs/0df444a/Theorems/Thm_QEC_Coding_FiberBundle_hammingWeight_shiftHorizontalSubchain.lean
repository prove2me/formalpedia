-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_shiftHorizontalSubchain
-- name    : QEC.Coding.FiberBundle.hammingWeight_shiftHorizontalSubchain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:31.316637+00:00
-- url     : https://prove2.me/theorems/9e6a060e-f251-410c-bc9e-e9528dae6f1b
-- title:
--   Fiber Bundle: hamming Weight shift Horizontal Subchain
-- statement:
--   A horizontal shift preserves Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1505-L1519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1505-L1519

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_shiftHorizontalSubchain
    {baseOne : Type u} [Fintype baseOne]
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    HammingWeight (shiftHorizontalSubchain n h) =
      HammingWeight h := by sorry
