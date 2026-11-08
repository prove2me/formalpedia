-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_distance_three_fifths
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.distance_three_fifths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:18:48.715971+00:00
-- url     : https://prove2.me/theorems/edca8fa5-bfae-4de5-99a3-30123f99ac44
-- title:
--   HHO20 Distance Balancing: distance three fifths
-- statement:
--   Exact fifth-power form of `D = Ω(N^(3/5)/polylog N)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L548-L567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L548-L567

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.distance_three_fifths
    (s N D : Nat) (hs : 200 ≤ s)
    (hN : N ≤ blocklengthScaleAt s)
    (hD : distanceScaleAt s ≤ D) :
    N ^ 3 ≤ distanceTradeoffCoefficient * s ^ 32 * D ^ 5 := by sorry
