-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initial_z_distance_tradeoff
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.initial_z_distance_tradeoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:43:23.349884+00:00
-- url     : https://prove2.me/theorems/a1b80856-267a-4b39-a2df-4bb03b972693
-- title:
--   HHO20 Distance Balancing: initial z distance tradeoff
-- statement:
--   Power-law form of `d_Z = Omega(N^(3/4) / poly(s))` for the unreduced
--   family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L465-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L465-L513

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.initial_z_distance_tradeoff
    (s N D : Nat) (hs : 200 ≤ s)
    (hN : N ≤ initialBlocklengthAt s)
    (hD : initialZDistanceScaleAt s ≤ D) :
    N ^ 3 ≤ initialZTradeoffCoefficient * s ^ 8 * D ^ 4 := by sorry
