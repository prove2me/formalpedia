-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_linearMap_apply_input_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.linearMap_apply_input_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:20.16399+00:00
-- url     : https://prove2.me/theorems/43d65bd7-74fc-4256-ba8c-707c14812a69
-- title:
--   HH18 Parameterized: linear Map apply input of explicit support
-- statement:
--   A linear operator map transports an explicitly supported finite mixture
--   to the corresponding pointwise mixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/EndpointSupport.lean#L22-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/EndpointSupport.lean#L22-L35

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18Parameterized.linearMap_apply_input_of_explicit_support
    {ι H K : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (linearMap : Operator H →ₗ[Complex] Operator K) (input : Operator H)
    (weight : ι → Complex) (inputSummand : ι → Operator H)
    (outputSummand : ι → Operator K)
    (hinput : input = support.sum (fun i => weight i • inputSummand i))
    (hpointwise : ∀ i, linearMap (inputSummand i) = outputSummand i) :
    linearMap input = support.sum (fun i => weight i • outputSummand i) := by sorry
