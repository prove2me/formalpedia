-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_boundary2_eq_zero
-- name    : QEC.Coding.FiberBundle.homologyBaseProjection_boundary2_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:23.039593+00:00
-- url     : https://prove2.me/theorems/9ed7f0fb-bbfa-4bdb-8c10-45f6bc5483e9
-- title:
--   Fiber Bundle: homology Base Projection boundary2 eq zero
-- statement:
--   If every fiber one-cell has even boundary parity, the bundle projection kills
--   every total-degree-two boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L61-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L61-L78

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.homologyBaseProjection_boundary2_eq_zero
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (hFiberParity : ∀ j : fiberOne, (∑ i : fiberZero,
      D.fiberBoundary i j) = 0)
    (c : Word (ZMod 2) (C2Index baseOne fiberOne)) :
    homologyBaseProjection (boundary2 D c) = 0 := by sorry
