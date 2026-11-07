-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_complex_of_real_sum_of_explicit_support
-- name    : QEC.Distillation.HH18Parameterized.complex_of_real_sum_of_explicit_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:05:42.947658+00:00
-- url     : https://prove2.me/theorems/e056e199-53d7-48e1-bb4a-aeeef4ca4d8f
-- title:
--   HH18 Parameterized: complex of real sum of explicit support
-- statement:
--   Cast a real explicit-support mass sum to the corresponding complex sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L23-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorSupport.lean#L23-L34

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

theorem QEC.Distillation.HH18Parameterized.complex_of_real_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] (support : Finset ι)
    (mass : ℝ) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected]
    (hmass : mass = support.sum (fun i =>
      if selected i then weight i else 0)) :
    (mass : Complex) = support.sum (fun i =>
      if selected i then (weight i : Complex) else 0) := by sorry
