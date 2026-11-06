-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex
-- name    : QEC.Coding.FiberBundle.card_qubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:46.538096+00:00
-- url     : https://prove2.me/theorems/100dc3af-a983-40e8-8db3-8648824e9c24
-- title:
--   Fiber Bundle: card qubit Index
-- statement:
--   The exact two-block number of total-degree-one coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L63-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L63-L70

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_qubitIndex
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne] :
    Fintype.card (QubitIndex baseZero baseOne fiberZero fiberOne) =
      Fintype.card baseOne * Fintype.card fiberZero +
        Fintype.card baseZero * Fintype.card fiberOne := by sorry
