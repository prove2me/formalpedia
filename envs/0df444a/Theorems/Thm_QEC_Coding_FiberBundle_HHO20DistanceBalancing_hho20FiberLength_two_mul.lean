-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_hho20FiberLength_two_mul
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.hho20FiberLength_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:41:19.999894+00:00
-- url     : https://prove2.me/theorems/ec6a4e8a-4c3e-44be-8286-014c7c13f2bb
-- title:
--   HHO20 Distance Balancing: hho20 Fiber Length two mul
-- statement:
--   The HHO20 Distance Balancing construction uses the hho20 Fiber Length two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L80-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L80-L84

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.hho20FiberLength_two_mul (s : Nat) :
    RandomPartition.hho20FiberLength (2 * s) =
      RandomPartition.hho20FiberLength s ^ 2 := by sorry
