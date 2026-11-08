-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initialXDistanceScaleAt_le_source
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.initialXDistanceScaleAt_le_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:42:41.305204+00:00
-- url     : https://prove2.me/theorems/cdd599ca-a490-4efe-ae34-c4eb01edeba4
-- title:
--   HHO20 Distance Balancing: initial XDistance Scale At le source
-- statement:
--   The explicit unreduced X-distance scale lies below the source's two
--   cohomological alternatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L370-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L370-L394

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.initialXDistanceScaleAt_le_source
    (s : Nat) (hs : 200 ≤ s) :
    initialXDistanceScaleAt s ≤
      min (RandomPartition.hho20FiberLength s ^ 2 / 2)
        ((6 * RandomPartition.hho20BaseScale s) /
          (100000 * RandomPartition.hho20DegreeScale s)) := by sorry
