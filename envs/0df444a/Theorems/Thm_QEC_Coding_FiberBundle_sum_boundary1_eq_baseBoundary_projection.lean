-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_sum_boundary1_eq_baseBoundary_projection
-- name    : QEC.Coding.FiberBundle.sum_boundary1_eq_baseBoundary_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:50.96721+00:00
-- url     : https://prove2.me/theorems/bf165514-7627-45df-8ce9-b92e5d3e11f9
-- title:
--   Fiber Bundle: sum boundary1 eq base Boundary projection
-- statement:
--   Summing the bundle cycle equation over one complete fiber leaves exactly the
--   base boundary of the horizontal projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L150-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L150-L188

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.sum_boundary1_eq_baseBoundary_projection
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
    (a : baseZero) :
    (∑ i : fiberZero, boundary1 D z (a, i)) =
      ∑ b : baseOne,
        homologyBaseProjection z b * D.baseBoundary a b := by sorry
