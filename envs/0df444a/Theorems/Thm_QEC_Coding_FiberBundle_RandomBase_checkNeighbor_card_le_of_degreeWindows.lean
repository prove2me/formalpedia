-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_checkNeighbor_card_le_of_degreeWindows
-- name    : QEC.Coding.FiberBundle.RandomBase.checkNeighbor_card_le_of_degreeWindows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:28.587116+00:00
-- url     : https://prove2.me/theorems/2c8f364a-57bf-4ad3-aa07-b7b9e6237da7
-- title:
--   Random Base: check Neighbor card le of degree Windows
-- statement:
--   The check-side degree needed by cohomological distance transport has an
--   explicit construction-owned bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5550-L5560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5550-L5560

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.checkNeighbor_card_le_of_degreeWindows
    {r Delta : Nat} (sample : Sample r)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (a : Fin (3 * r)) :
    Fintype.card
        (ClassicalWeightReduction.CheckNeighbor
          (incidenceRelation sample) a) ≤
      101 * Delta := by sorry
