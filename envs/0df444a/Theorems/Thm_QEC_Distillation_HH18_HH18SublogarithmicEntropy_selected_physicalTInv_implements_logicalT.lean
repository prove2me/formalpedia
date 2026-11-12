-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_physicalTInv_implements_logicalT
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_physicalTInv_implements_logicalT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:32:24.293204+00:00
-- url     : https://prove2.me/theorems/c7ec606b-e3cf-4341-b946-20554391c105
-- title:
--   HH18 Sublogarithmic Entropy: selected physical TInv implements logical T
-- statement:
--   Logical T is obtained only through the proved inverse physical action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L94-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L94-L102

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding
open Coding.PuncturedReedMuller
open QEC.Distillation.HH18PuncturedReedMuller

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_physicalTInv_implements_logicalT (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    (selectedEncodedCode A D j hA hD hwindow hj).ImplementsLogicalGate
      (physicalTInv (parameterW A j) (parameterM D j))
      (logicalT (parameterW A j) (parameterM D j)) := by sorry
