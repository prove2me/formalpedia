-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_dimensionScale_le_baseScale_product
-- name    : QEC.Coding.FiberBundle.HHO20DistanceBalancing.dimensionScale_le_baseScale_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:17:32.663457+00:00
-- url     : https://prove2.me/theorems/e53bb4ab-7471-4d0c-a638-08d3d26b84db
-- title:
--   HHO20 Distance Balancing: dimension Scale le base Scale product
-- statement:
--   The product of the two construction dimensions contains `2^(6s)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L119-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Asymptotics.lean#L119-L136

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u

theorem QEC.Coding.FiberBundle.HHO20DistanceBalancing.dimensionScale_le_baseScale_product
    (s : Nat) (hs : 200 ≤ s) :
    dimensionScaleAt s ≤
      RandomPartition.hho20BaseScale (2 * s) *
        RandomPartition.hho20BaseScale s := by sorry
