-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_boundary2_apply_vertical
-- name    : QEC.Coding.FiberBundle.boundary2_apply_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:44:40.339497+00:00
-- url     : https://prove2.me/theorems/f212d9c9-8365-47d4-942d-265ad08229b8
-- title:
--   Fiber Bundle: boundary2 apply vertical
-- statement:
--   Vertical coordinate formula for a general bundle two-boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L539-L568
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L539-L568

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.boundary2_apply_vertical
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (c : Word (ZMod 2) (C2Index baseOne fiberOne))
    (a : baseZero) (j : fiberOne) :
    boundary2 D c (Sum.inr (a, j)) =
      ∑ b : baseOne,
        D.baseBoundary a b *
          c (b, (D.connection b a).onOne.symm j) := by sorry
