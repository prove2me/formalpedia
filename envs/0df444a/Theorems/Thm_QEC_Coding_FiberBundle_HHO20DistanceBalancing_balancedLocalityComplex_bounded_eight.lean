-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedLocalityComplex_bounded_eight
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedLocalityComplex_bounded_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:17:06.486842+00:00
-- url     : https://prove2.me/theorems/c545743d-8430-4369-a40d-642eb204c3f3
-- title:
--   HHO20 Distance Balancing: balanced Locality Complex bounded eight
-- statement:
--   Exact constant qLDPC locality for the final HHO20--EKZ construction:
--   weight reduction contributes `5`, the classical balancing factor contributes
--   `3`, and the product bound adds them.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean#L178-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean#L178-L199

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedLocalityComplex_bounded_eight
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (balancedLocalityComplex
          baseSample twistSample balanceSample)).localityProfile 8 := by sorry
