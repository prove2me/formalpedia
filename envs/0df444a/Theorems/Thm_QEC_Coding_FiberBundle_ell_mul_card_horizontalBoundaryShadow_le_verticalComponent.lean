-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
-- name    : QEC.Coding.FiberBundle.ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:47:42.733232+00:00
-- url     : https://prove2.me/theorems/386f0074-3b55-4265-ac66-ea987570a59a
-- title:
--   Fiber Bundle: ell mul card horizontal Boundary Shadow le vertical Component
-- statement:
--   After sliding, vertical weight is at least `ell` times the number of base
--   zero-cells on which the horizontal boundary is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2954-L2985
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2954-L2985

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z) :
    ell *
        (horizontalBoundaryShadow baseSample twistSample
          (horizontalComponent z)).card ≤
      HammingWeight (verticalComponent z) := by sorry
