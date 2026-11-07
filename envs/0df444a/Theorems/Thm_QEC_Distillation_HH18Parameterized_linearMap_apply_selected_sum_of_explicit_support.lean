-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_linearMap_apply_selected_sum_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.linearMap_apply_selected_sum_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:37.428106+00:00
-- url     : https://prove2.me/theorems/0904d3ad-cd75-4aeb-819d-64560f42c0fa
-- title:
--   HH18 Parameterized: linear Map apply selected sum of explicit support
-- statement:
--   Apply a linear operator map through one explicitly selected finite sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L37-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L37-L56

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u v w

theorem QEC.Distillation.HH18Parameterized.linearMap_apply_selected_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (support : Finset ι) (linearMap : Operator H →ₗ[Complex] Operator K)
    (input : Operator H) (weight : ι → Complex) (selected : ι → Prop)
    [DecidablePred selected] (inputBranch : ι → Operator H)
    (outputBranch : ι → Operator K)
    (hinput : input = support.sum (fun i =>
      if selected i then weight i • inputBranch i else 0))
    (hpointwise : ∀ i, linearMap (inputBranch i) = outputBranch i) :
    linearMap input = support.sum (fun i =>
      if selected i then weight i • outputBranch i else 0) := by sorry
