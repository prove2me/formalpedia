-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_bitNeighbor_card_le_of_degreeWindows
-- name    : QEC.Coding.FiberBundle.RandomBase.bitNeighbor_card_le_of_degreeWindows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:08:32.375829+00:00
-- url     : https://prove2.me/theorems/e93d0f36-4bea-44c8-bea6-e779195b4a71
-- title:
--   Random Base: bit Neighbor card le of degree Windows
-- statement:
--   The variable-side degree has the same convenient common upper bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5563-L5573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L5563-L5573

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.bitNeighbor_card_le_of_degreeWindows
    {r Delta : Nat} (sample : Sample r)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (b : Fin (4 * r)) :
    Fintype.card
        (ClassicalWeightReduction.BitNeighbor
          (incidenceRelation sample) b) ≤
      101 * Delta := by sorry
