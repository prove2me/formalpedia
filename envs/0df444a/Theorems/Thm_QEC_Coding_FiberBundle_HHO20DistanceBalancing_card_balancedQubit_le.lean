-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_card_balancedQubit_le
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.card_balancedQubit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:39:25.889501+00:00
-- url     : https://prove2.me/theorems/84618d20-c660-42c2-a58f-5025e4baeb52
-- title:
--   HHO20 Distance Balancing: card balanced Qubit le
-- statement:
--   Explicit blocklength bound for the finite balanced product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L280-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/DistanceBalancing.lean#L280-L336

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.card_balancedQubit_le
    {rMain typeCount ell DeltaMain rBalance DeltaBalance : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample rMain)
    (twistSample : RandomTwist.Sample rMain typeCount ell)
    (balanceSample : RandomBase.Sample rBalance)
    (hMainGood : RandomBase.IsFullyGood
      (Delta := DeltaMain) baseSample)
    (hBalanceGood : RandomBase.IsFullyGood
      (Delta := DeltaBalance) balanceSample) :
    Fintype.card
        (DistanceBalancing.QubitIndex
          (MainQubit baseSample twistSample)
          (MainCZero baseSample twistSample)
          (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
      2611456 * rMain * DeltaMain * (ell * ell) *
        rBalance * DeltaBalance := by sorry
