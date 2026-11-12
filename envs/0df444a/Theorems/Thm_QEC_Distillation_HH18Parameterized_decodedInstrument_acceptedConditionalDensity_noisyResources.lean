-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_acceptedConditionalDensity_noisyResources
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_acceptedConditionalDensity_noisyResources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:20:07.329662+00:00
-- url     : https://prove2.me/theorems/e248288d-3d3f-47d9-aa57-7c7ec7442e69
-- title:
--   HH18 Parameterized: decoded Instrument accepted Conditional Density noisy Resources
-- statement:
--   The genuine positive accepted conditional density of the decoded finite
--   instrument is exactly the physical normalized accepted decoded output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L88-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L88-L108

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_prepareMeasuredResources
import Theorems.Thm_QEC_Distillation_HH18Parameterized_endpointWeight_accepted_pos

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_acceptedConditionalDensity_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (decodedInstrument h hdegree).conditionalDensity .accepted
        (prepareMeasuredResources m w (noisyResources m w epsilon))
        (by
          rw [decodedInstrument_bornWeight_prepareMeasuredResources]
          exact endpointWeight_accepted_pos h hdegree epsilon) =
      (resourceDecodedRun h hdegree
        (noisyResources m w epsilon)).acceptedOutput := by sorry
