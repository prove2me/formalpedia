-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
-- name    : QEC.Coding.FiberBundle.horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:50.487251+00:00
-- url     : https://prove2.me/theorems/6c5d10ff-9ad2-473c-9de8-a37c37de1864
-- title:
--   Fiber Bundle: horizontal Base Lift add bundle Coboundary erase C0 Fiber
-- statement:
--   Dropping one shadow fiber produces a cohomologous representative by adding
--   one explicit bundle coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L690-L715
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L690-L715

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (x : Word (ZMod 2) baseOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x +
        bundleCoboundary D (eraseC0Fiber u a) =
      (horizontalBaseLift
            (baseZero := baseZero) (fiberZero := fiberZero)
            (fiberOne := fiberOne) x +
          bundleCoboundary D u) +
        bundleCoboundary D (eraseC0FiberCorrection u a) := by sorry
