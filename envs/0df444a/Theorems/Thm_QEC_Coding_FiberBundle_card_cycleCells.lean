-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_cycleCells
-- name    : QEC.Coding.FiberBundle.card_cycleCells
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:59.01629+00:00
-- url     : https://prove2.me/theorems/59bcacb9-b14f-434e-8157-37cdd48f0019
-- title:
--   Fiber Bundle: card cycle Cells
-- statement:
--   A cycle of length `n` has exactly `n` zero-cells and `n` one-cells.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L501-L503
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L501-L503

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_cycleCells (n : Nat) [NeZero n] :
    Fintype.card (ZMod n) = n := by sorry
