-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
-- name    : QEC.Coding.FiberBundle.ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:22.05578+00:00
-- url     : https://prove2.me/theorems/e2e7e013-f69a-4568-830a-ea0dff5140a8
-- title:
--   Fiber Bundle: ell mul horizontal Component le 500 mul vertical Component of twist Graph LTC
-- statement:
--   The quantitative version retaining the HHO20 string-length factor:
--   `ell * |h| ≤ 500 * |v|` in the small-word LTC regime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3039-L3085
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L3039-L3085

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hNormalized : IsHorizontallyResidueNormalized z)
    (hSmall :
      5000 * Delta * HammingWeight (horizontalComponent z) ≤
        ell * (4 * r)) :
    ell * HammingWeight (horizontalComponent z) ≤
      500 * HammingWeight (verticalComponent z) := by sorry
