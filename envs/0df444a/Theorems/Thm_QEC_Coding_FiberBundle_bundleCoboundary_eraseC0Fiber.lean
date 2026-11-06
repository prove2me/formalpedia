-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_eraseC0Fiber
-- name    : QEC.Coding.FiberBundle.bundleCoboundary_eraseC0Fiber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:55:50.000208+00:00
-- url     : https://prove2.me/theorems/fe9560c4-a9dd-4a46-8a32-fb01342b7353
-- title:
--   Fiber Bundle: bundle Coboundary erase C0 Fiber
-- statement:
--   Erasing one zero-cell fiber changes its bundle coboundary by the explicit correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L670-L684
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L670-L684

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.bundleCoboundary_eraseC0Fiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    bundleCoboundary D (eraseC0Fiber u a) =
      bundleCoboundary D u +
        bundleCoboundary D (eraseC0FiberCorrection u a) := by sorry
