-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_baseBoundary_projection_eq_zero_of_boundary1_eq_zero
-- name    : QEC.Coding.FiberBundle.baseBoundary_projection_eq_zero_of_boundary1_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:41.145325+00:00
-- url     : https://prove2.me/theorems/76e08270-9cdd-4162-954f-47b2ec40ec9a
-- title:
--   Fiber Bundle: base Boundary projection eq zero of boundary1 eq zero
-- statement:
--   A bundle cycle projects to a cycle of the base complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L191-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L191-L207

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.baseBoundary_projection_eq_zero_of_boundary1_eq_zero
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (hFiberParity : ∀ j : fiberOne, (∑ i : fiberZero,
      D.fiberBoundary i j) = 0)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (hz : boundary1 D z = 0)
    (a : baseZero) :
    (∑ b : baseOne,
      homologyBaseProjection z b * D.baseBoundary a b) = 0 := by sorry
