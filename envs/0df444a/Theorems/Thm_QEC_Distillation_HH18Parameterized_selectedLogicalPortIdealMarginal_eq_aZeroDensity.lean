-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortIdealMarginal_eq_aZeroDensity
-- name    : QEC.Distillation.HH18Parameterized.selectedLogicalPortIdealMarginal_eq_aZeroDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:05:57.381771+00:00
-- url     : https://prove2.me/theorems/05422df2-e7e8-4db6-9a8f-8c29936cffe4
-- title:
--   HH18 Parameterized: selected Logical Port Ideal Marginal eq a Zero Density
-- statement:
--   The HH18 Parameterized construction uses the selected Logical Port Ideal Marginal eq a Zero Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L393-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPort.lean#L393-L411

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.selectedLogicalPortIdealMarginal_eq_aZeroDensity (m w : Nat)
    (port : LogicalSite m w) :
    selectedLogicalPortIdealMarginal m w port = aZeroDensity := by sorry
