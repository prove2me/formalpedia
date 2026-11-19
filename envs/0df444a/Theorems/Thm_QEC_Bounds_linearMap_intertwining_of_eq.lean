-- Prove2me | Theorems.Thm_QEC_Bounds_linearMap_intertwining_of_eq
-- name    : QEC.Bounds.linearMap_intertwining_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T07:03:25.457812+00:00
-- url     : https://prove2.me/theorems/ea27751d-385a-48cc-8bc4-2ec06c7d9de7
-- title:
--   Bounds: linear Map intertwining of eq
-- statement:
--   The Bounds construction uses the linear Map intertwining of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/IntertwiningAlgebra.lean#L49-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Assembly/IntertwiningAlgebra.lean#L49-L59

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_JointCoordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_IntertwiningAlgebra
set_option autoImplicit false
open QEC
open QEC.Bounds
universe u

theorem QEC.Bounds.linearMap_intertwining_of_eq
    {H K : Type u}
    [AddCommMonoid H] [Module Complex H]
    [AddCommMonoid K] [Module Complex K]
    (embedding coordinates : H →ₗ[Complex] K)
    (physical : K →ₗ[Complex] K) (logical : H →ₗ[Complex] H)
    (hembedding : embedding = coordinates)
    (hcoordinates : physical.comp coordinates = coordinates.comp logical) :
    physical.comp embedding = embedding.comp logical := by sorry
