-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_binaryCSSCode_stabilizer_isSourceValidBinary
-- name    : QEC.Coding.FiberBundle.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:44.287994+00:00
-- url     : https://prove2.me/theorems/1892d372-68f3-4b37-86a7-99b1ae5957b1
-- title:
--   Fiber Bundle: binary CSSCode stabilizer is Source Valid Binary
-- statement:
--   The exact induced stabilizer satisfies the repository's binary source-validity contract.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L337-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L337-L345

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.binaryCSSCode_stabilizer_isSourceValidBinary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by sorry
