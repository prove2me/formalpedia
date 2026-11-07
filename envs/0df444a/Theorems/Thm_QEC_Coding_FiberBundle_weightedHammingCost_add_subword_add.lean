-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightedHammingCost_add_subword_add
-- name    : QEC.Coding.FiberBundle.weightedHammingCost_add_subword_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:50:57.240746+00:00
-- url     : https://prove2.me/theorems/b5840380-c0a0-4589-b9fb-2d7061aa6963
-- title:
--   Fiber Bundle: weighted Hamming Cost add subword add
-- statement:
--   Deleting a binary subword partitions every weighted support cost exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1443-L1471
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/HomologyRepresentatives.lean#L1443-L1471

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.weightedHammingCost_add_subword_add
    {ι : Type u} [Fintype ι]
    (weight : ι → Nat)
    (h z : Word (ZMod 2) ι)
    (hhz : IsBinarySubword h z) :
    WeightedHammingCost weight (z + h) +
        WeightedHammingCost weight h =
      WeightedHammingCost weight z := by sorry
