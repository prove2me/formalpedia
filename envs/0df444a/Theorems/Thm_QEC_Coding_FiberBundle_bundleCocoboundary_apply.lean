-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_bundleCocoboundary_apply
-- name    : QEC.Coding.FiberBundle.bundleCocoboundary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:06:49.944203+00:00
-- url     : https://prove2.me/theorems/9483612f-f433-4606-8ab1-34591bc476fa
-- title:
--   Fiber Bundle: bundle Cocoboundary apply
-- statement:
--   Coordinate formula for the transpose of the second bundle boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L159-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L159-L178

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.bundleCocoboundary_apply
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (bj : C2Index baseOne fiberOne) :
    bundleCocoboundary D z bj =
      ∑ q : QubitIndex baseZero baseOne fiberZero fiberOne,
        z q * boundary2Matrix D q bj := by sorry
