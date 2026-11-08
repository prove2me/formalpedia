-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initialZDistanceScaleAt_le_source
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.initialZDistanceScaleAt_le_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:42:30.294877+00:00
-- url     : https://prove2.me/theorems/6d474426-7562-4014-82d2-9a719f87a36c
-- title:
--   HHO20 Distance Balancing: initial ZDistance Scale At le source
-- statement:
--   The explicit unreduced Z-distance scale lies below the source homology
--   bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L398-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L398-L418

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.initialZDistanceScaleAt_le_source
    (s : Nat) (hs : 200 ≤ s) :
    initialZDistanceScaleAt s ≤
      (RandomPartition.hho20FiberLength s *
        (4 * RandomPartition.hho20BaseScale s)) /
          (5000 * RandomPartition.hho20DegreeScale s) := by sorry
