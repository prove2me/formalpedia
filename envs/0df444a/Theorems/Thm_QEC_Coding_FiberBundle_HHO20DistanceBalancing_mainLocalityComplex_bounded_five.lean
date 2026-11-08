-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_mainLocalityComplex_bounded_five
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.mainLocalityComplex_bounded_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:41:03.2481+00:00
-- url     : https://prove2.me/theorems/52076a77-b587-4090-99a2-93375834b509
-- title:
--   HHO20 Distance Balancing: main Locality Complex bounded five
-- statement:
--   HHO20 weight reduction makes every main-complex check and physical-qubit
--   incidence have size at most five.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean#L105-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean#L105-L145

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.mainLocalityComplex_bounded_five
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (mainLocalityComplex baseSample twistSample)).localityProfile 5 := by sorry
