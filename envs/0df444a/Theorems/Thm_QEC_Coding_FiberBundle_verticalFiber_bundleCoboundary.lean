-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_verticalFiber_bundleCoboundary
-- name    : QEC.Coding.FiberBundle.verticalFiber_bundleCoboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:56:27.442084+00:00
-- url     : https://prove2.me/theorems/67c4281d-c82d-4329-8141-08e81d5d891b
-- title:
--   Fiber Bundle: vertical Fiber bundle Coboundary
-- statement:
--   The vertical fiber of a bundle coboundary is the ordinary fiber coboundary of
--   the word over that base zero-cell.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1107-L1124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1107-L1124

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.verticalFiber_bundleCoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) (j : fiberOne) :
    verticalFiber (bundleCoboundary D u) a j =
      ∑ i : fiberZero, u (a, i) * D.fiberBoundary i j := by sorry
