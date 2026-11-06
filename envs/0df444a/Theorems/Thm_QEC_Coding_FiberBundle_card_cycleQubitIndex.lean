-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_cycleQubitIndex
-- name    : QEC.Coding.FiberBundle.card_cycleQubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:56.962794+00:00
-- url     : https://prove2.me/theorems/f83017d8-0669-45f3-95ce-09e13256d183
-- title:
--   Fiber Bundle: card cycle Qubit Index
-- statement:
--   The exact HHO20 two-block qubit count for a cycle fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L506-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L506-L513

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_cycleQubitIndex
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n] :
    Fintype.card
      (QubitIndex baseZero baseOne (ZMod n) (ZMod n)) =
      Fintype.card baseOne * n + Fintype.card baseZero * n := by sorry
