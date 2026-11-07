-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_backwardShiftHorizontalSubchain
-- name    : QEC.Coding.FiberBundle.hammingWeight_backwardShiftHorizontalSubchain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:51:31.228193+00:00
-- url     : https://prove2.me/theorems/69d5905e-951d-4b93-a1fe-395fe1cd94e7
-- title:
--   Fiber Bundle: hamming Weight backward Shift Horizontal Subchain
-- statement:
--   A backward horizontal shift preserves Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1903-L1917
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1903-L1917

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.hammingWeight_backwardShiftHorizontalSubchain
    {baseOne : Type u} [Fintype baseOne]
    (n : Nat) [NeZero n]
    (h : Word (ZMod 2) (baseOne × ZMod n)) :
    HammingWeight (backwardShiftHorizontalSubchain n h) =
      HammingWeight h := by sorry
