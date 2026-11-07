-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_horizontalComponent_le_250_mul_verticalComponent_of_twistGraphLTC
-- name    : QEC.Coding.FiberBundle.horizontalComponent_le_250_mul_verticalComponent_of_twistGraphLTC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:08:33.699896+00:00
-- url     : https://prove2.me/theorems/c2ed7c90-eed4-48cf-98af-689086dbc063
-- title:
--   Fiber Bundle: horizontal Component le 250 mul vertical Component of twist Graph LTC
-- statement:
--   Conditional deterministic closure of the HHO20 twist-graph step: once the
--   internally proved LTC good event is available, every sufficiently light
--   normalized horizontal sector is controlled by the real vertical weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2992-L3033
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2992-L3033

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.horizontalComponent_le_250_mul_verticalComponent_of_twistGraphLTC
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
    HammingWeight (horizontalComponent z) ≤
      250 * HammingWeight (verticalComponent z) := by sorry
