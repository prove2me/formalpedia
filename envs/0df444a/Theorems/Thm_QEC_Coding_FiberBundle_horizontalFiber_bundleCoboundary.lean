-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_bundleCoboundary
-- name    : QEC.Coding.FiberBundle.horizontalFiber_bundleCoboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:53.089513+00:00
-- url     : https://prove2.me/theorems/6015dcc1-9519-47e2-b74a-2a437bae589a
-- title:
--   Fiber Bundle: horizontal Fiber bundle Coboundary
-- statement:
--   The horizontal fiber of a bundle coboundary is the sum of the incident base
--   zero-cell fiber words, each reindexed by its selected connection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L721-L737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L721-L737

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalFiber_bundleCoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (b : baseOne) (j : fiberZero) :
    horizontalFiber (bundleCoboundary D u) b j =
      ∑ a : baseZero,
        u (a, (D.connection b a).onZero j) * D.baseBoundary a b := by sorry
