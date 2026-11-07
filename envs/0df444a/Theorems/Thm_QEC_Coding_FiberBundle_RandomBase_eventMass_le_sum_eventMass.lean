-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_eventMass_le_sum_eventMass
-- name    : QEC.Coding.FiberBundle.RandomBase.eventMass_le_sum_eventMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:05.882965+00:00
-- url     : https://prove2.me/theorems/e98978d4-9b00-491c-913a-cd745fd05049
-- title:
--   Random Base: event Mass le sum event Mass
-- statement:
--   A finite cover of an event gives a union bound on its probability mass.  This
--   is the event-side companion of `failureMass_le_sum_eventMass`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L768-L787
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L768-L787

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.eventMass_le_sum_eventMass
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (event : Ω → Prop) [DecidablePred event]
    (cover : ι → Ω → Prop) [∀ i, DecidablePred (cover i)]
    (hcover : ∀ ω, event ω → ∃ i, cover i ω) :
    eventMass p event ≤ ∑ i, eventMass p (cover i) := by sorry
