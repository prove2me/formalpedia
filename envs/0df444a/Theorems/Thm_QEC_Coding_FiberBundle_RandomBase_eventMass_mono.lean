-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_mono
-- name    : QEC.Coding.FiberBundle.RandomBase.eventMass_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:43.160824+00:00
-- url     : https://prove2.me/theorems/92c310de-7b0a-4320-928a-fd5315f7c28d
-- title:
--   Random Base: event Mass mono
-- statement:
--   Finite event mass is monotone under pointwise event inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1061-L1069
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L1061-L1069

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.eventMass_mono
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (left right : Ω → Prop)
    [DecidablePred left] [DecidablePred right]
    (h : ∀ ω, left ω → right ω) :
    eventMass p left ≤ eventMass p right := by sorry
