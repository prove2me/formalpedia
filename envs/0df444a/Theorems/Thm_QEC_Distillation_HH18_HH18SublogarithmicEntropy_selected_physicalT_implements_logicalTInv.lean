-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_physicalT_implements_logicalTInv
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_physicalT_implements_logicalTInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:33:13.347555+00:00
-- url     : https://prove2.me/theorems/29c940a7-c563-4d74-965a-5d8ee3c0f964
-- title:
--   HH18 Sublogarithmic Entropy: selected physical T implements logical TInv
-- statement:
--   Simultaneous physical T implements simultaneous logical T-dagger.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L83-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L83-L91

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding
open Coding.PuncturedReedMuller
open QEC.Distillation.HH18PuncturedReedMuller

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_physicalT_implements_logicalTInv (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    (selectedEncodedCode A D j hA hD hwindow hj).ImplementsLogicalGate
      (physicalT (parameterW A j) (parameterM D j))
      (logicalTInv (parameterW A j) (parameterM D j)) := by sorry
