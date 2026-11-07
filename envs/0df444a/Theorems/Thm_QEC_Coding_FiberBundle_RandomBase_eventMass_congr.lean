-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_congr
-- name    : QEC.Coding.FiberBundle.RandomBase.eventMass_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:46:46.198204+00:00
-- url     : https://prove2.me/theorems/78f6c370-93cb-46ec-b4b4-e40f2a26d9d8
-- title:
--   Random Base: event Mass congr
-- statement:
--   Finite event mass respects pointwise logical equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L475-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L475-L486

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.eventMass_congr
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (left right : Ω → Prop)
    [DecidablePred left] [DecidablePred right]
    (h : ∀ ω, left ω ↔ right ω) :
    eventMass p left = eventMass p right := by sorry
