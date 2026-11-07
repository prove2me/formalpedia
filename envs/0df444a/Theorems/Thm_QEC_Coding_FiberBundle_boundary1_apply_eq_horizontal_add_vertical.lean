-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_boundary1_apply_eq_horizontal_add_vertical
-- name    : QEC.Coding.FiberBundle.boundary1_apply_eq_horizontal_add_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:44:43.29684+00:00
-- url     : https://prove2.me/theorems/22456f08-5a9e-4fef-9bd4-4f11c07cc81d
-- title:
--   Fiber Bundle: boundary1 apply eq horizontal add vertical
-- statement:
--   Coordinate formula for the first bundle boundary, split by cell sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L108-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L108-L144

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.boundary1_apply_eq_horizontal_add_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne))
    (a : baseZero) (i : fiberZero) :
    boundary1 D z (a, i) =
      (∑ b : baseOne,
        D.baseBoundary a b *
          z (Sum.inl (b, (D.connection b a).onZero.symm i))) +
      ∑ j : fiberOne, D.fiberBoundary i j * z (Sum.inr (a, j)) := by sorry
