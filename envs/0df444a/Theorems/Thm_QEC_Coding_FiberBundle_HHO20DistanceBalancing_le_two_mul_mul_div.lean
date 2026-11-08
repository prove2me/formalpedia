-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_le_two_mul_mul_div
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.le_two_mul_mul_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:41:39.189937+00:00
-- url     : https://prove2.me/theorems/3b696c78-bc4f-499c-8fc3-15ae9df00c15
-- title:
--   HHO20 Distance Balancing: le two mul mul div
-- statement:
--   A quotient loses at most a factor two once its denominator fits in its
--   numerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L273-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L273-L286

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.le_two_mul_mul_div
    (a d : Nat) (hd : 0 < d) (hda : d ≤ a) :
    a ≤ 2 * d * (a / d) := by sorry
