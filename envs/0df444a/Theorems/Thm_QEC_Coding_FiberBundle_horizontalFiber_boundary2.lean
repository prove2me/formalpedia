-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_boundary2
-- name    : QEC.Coding.FiberBundle.horizontalFiber_boundary2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:43:42.302717+00:00
-- url     : https://prove2.me/theorems/e4eae504-dad2-4cf1-b84b-775dac1aa4a7
-- title:
--   Fiber Bundle: horizontal Fiber boundary2
-- statement:
--   The horizontal fiber of a bundle two-boundary is the fiber boundary of the
--   corresponding two-chain fiber.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L41-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L41-L55

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalFiber_boundary2
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (c : Word (ZMod 2) (C2Index baseOne fiberOne))
    (b : baseOne) (i : fiberZero) :
    horizontalFiber (boundary2 D c) b i =
      ∑ j : fiberOne, D.fiberBoundary i j * c (b, j) := by sorry
