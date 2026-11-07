-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
-- name    : QEC.Coding.FiberBundle.eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:48:57.153348+00:00
-- url     : https://prove2.me/theorems/e82083a2-2040-4316-be2a-84219a4cf124
-- title:
--   Fiber Bundle: eq vertical Fundamental Word of horizontal zero of vertical constant
-- statement:
--   A word with zero horizontal sector and constant vertical fibers is explicit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L511-L529
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L511-L529

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.eq_verticalFundamentalWord_of_horizontal_zero_of_vertical_constant
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hzHorizontal : ∀ b : Fin (4 * r), horizontalFiber z b = 0)
    (hzVertical : ∀ a : Fin (3 * r), ∀ j,
      verticalFiber z a j = verticalFiber z a 0) :
    z =
      verticalFundamentalWord
        (baseOne := Fin (4 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell))
        (verticalFundamentalCoefficient z) := by sorry
