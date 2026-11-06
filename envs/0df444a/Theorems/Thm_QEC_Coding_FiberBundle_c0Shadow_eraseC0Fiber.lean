-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_c0Shadow_eraseC0Fiber
-- name    : QEC.Coding.FiberBundle.c0Shadow_eraseC0Fiber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:55:44.270116+00:00
-- url     : https://prove2.me/theorems/b34a43b4-ebfb-4c19-affc-7a27e1f3aef7
-- title:
--   Fiber Bundle: c0 Shadow erase C0 Fiber
-- statement:
--   Erasing one fiber deletes exactly that point from the zero-cell shadow.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L523-L540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L523-L540

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.c0Shadow_eraseC0Fiber
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [DecidableEq baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    c0Shadow (eraseC0Fiber u a) = (c0Shadow u).erase a := by sorry
