-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
-- name    : QEC.Coding.FiberBundle.homologyBaseProjection_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:41:26.791264+00:00
-- url     : https://prove2.me/theorems/85d6828c-c930-4484-92b7-b2d6898f72a7
-- title:
--   Fiber Bundle: homology Base Projection add
-- statement:
--   The Fiber Bundle construction uses the homology Base Projection add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L27-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L27-L35

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.homologyBaseProjection_add
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype fiberZero]
    (z z' : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    homologyBaseProjection (z + z') =
      homologyBaseProjection z + homologyBaseProjection z' := by sorry
