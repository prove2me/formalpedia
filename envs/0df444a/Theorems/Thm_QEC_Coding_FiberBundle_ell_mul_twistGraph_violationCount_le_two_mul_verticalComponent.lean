-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
-- name    : QEC.Coding.FiberBundle.ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:52:59.775103+00:00
-- url     : https://prove2.me/theorems/d5d753cf-7162-42c1-b6e5-767af4a02c97
-- title:
--   Fiber Bundle: ell mul twist Graph violation Count le two mul vertical Component
-- statement:
--   Full quantitative vertical string bound: every violated twist check costs a
--   length-`ell` string, up to the unavoidable factor two for its endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2867-L2904
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L2867-L2904

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.ell_mul_twistGraph_violationCount_le_two_mul_verticalComponent
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
        TwistGraph.violationCount baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) ≤
      2 * HammingWeight (verticalComponent z) := by sorry
