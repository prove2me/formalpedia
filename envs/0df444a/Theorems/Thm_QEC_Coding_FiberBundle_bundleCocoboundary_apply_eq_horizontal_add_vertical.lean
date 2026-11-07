-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_bundleCocoboundary_apply_eq_horizontal_add_vertical
-- name    : QEC.Coding.FiberBundle.bundleCocoboundary_apply_eq_horizontal_add_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:06:25.325778+00:00
-- url     : https://prove2.me/theorems/9eb4d208-503a-4dc2-936d-8d2fc14df329
-- title:
--   Fiber Bundle: bundle Cocoboundary apply eq horizontal add vertical
-- statement:
--   The cocycle equation split into horizontal and vertical bundle sectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L181-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L181-L201

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.bundleCocoboundary_apply_eq_horizontal_add_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (b : baseOne) (j : fiberOne) :
    bundleCocoboundary D z (b, j) =
      (∑ i : fiberZero,
        z (Sum.inl (b, i)) * D.fiberBoundary i j) +
      ∑ a : baseZero,
        z (Sum.inr (a, (D.connection b a).onOne j)) *
          D.baseBoundary a b := by sorry
