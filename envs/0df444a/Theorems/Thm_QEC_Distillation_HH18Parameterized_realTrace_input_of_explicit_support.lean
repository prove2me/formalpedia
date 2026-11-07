-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_realTrace_input_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.realTrace_input_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:26.741673+00:00
-- url     : https://prove2.me/theorems/8b9de2b0-9696-40ee-b7a2-8e10a69ef6ec
-- title:
--   HH18 Parameterized: real Trace input of explicit support
-- statement:
--   The real trace of an explicitly supported finite sum is the finite sum of
--   its specified real trace summands.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/EndpointSupport.lean#L39-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/EndpointSupport.lean#L39-L50

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

theorem QEC.Distillation.HH18Parameterized.realTrace_input_of_explicit_support
    {ι H : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (input : Operator H) (inputSummand : ι → Operator H) (realSummand : ι → ℝ)
    (hinput : input = support.sum inputSummand)
    (hpointwise : ∀ i, Complex.re (LinearMap.trace Complex H (inputSummand i)) =
      realSummand i) :
    Complex.re (LinearMap.trace Complex H input) = support.sum realSummand := by sorry
