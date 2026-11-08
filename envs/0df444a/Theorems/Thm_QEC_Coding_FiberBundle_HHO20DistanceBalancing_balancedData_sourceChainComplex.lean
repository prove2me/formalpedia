-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedData_sourceChainComplex
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedData_sourceChainComplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:37:04.192197+00:00
-- url     : https://prove2.me/theorems/2e4ff922-5b22-4937-8a2b-abff6578f561
-- title:
--   HHO20 Distance Balancing: balanced Data source Chain Complex
-- statement:
--   The HHO20 Distance Balancing construction uses the balanced Data source Chain Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L129-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L129-L139

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedData_sourceChainComplex
    {rMain typeCount ell rBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance) :
    DistanceBalancing.sourceChainComplex
        (balancedData baseSample twistSample balanceSample) =
      dualChainComplex (mainComplex baseSample twistSample) := by sorry
