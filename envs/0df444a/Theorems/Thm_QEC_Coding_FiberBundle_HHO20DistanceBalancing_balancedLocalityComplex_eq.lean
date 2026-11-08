-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedLocalityComplex_eq
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedLocalityComplex_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:17:17.05891+00:00
-- url     : https://prove2.me/theorems/6aabf6e0-5fd6-4af6-a5ca-a449603e3663
-- title:
--   HHO20 Distance Balancing: balanced Locality Complex eq
-- statement:
--   The named final complex is definitionally the same EKZ product used by
--   the distance, dimension, and blocklength theorems.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean#L163-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancingLocality.lean#L163-L173

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedLocalityComplex_eq
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    balancedLocalityComplex baseSample twistSample balanceSample =
      DistanceBalancing.chainComplex
        (balancedData baseSample twistSample balanceSample) := by sorry
