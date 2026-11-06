-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_binaryCSSCode_finrank_carrier
-- name    : QEC.Coding.FiberBundle.binaryCSSCode_finrank_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:45.689186+00:00
-- url     : https://prove2.me/theorems/4c8a1ddf-c88f-4abf-916b-91bbaed330c0
-- title:
--   Fiber Bundle: binary CSSCode finrank carrier
-- statement:
--   The semantic carrier dimension is determined by middle homology.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L360-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L360-L371

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.binaryCSSCode_finrank_carrier
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Module.finrank Complex (binaryCSSCode D).stabilizer.code.carrier =
      2 ^ Module.finrank (ZMod 2) (chainComplex D).middleHomology := by sorry
