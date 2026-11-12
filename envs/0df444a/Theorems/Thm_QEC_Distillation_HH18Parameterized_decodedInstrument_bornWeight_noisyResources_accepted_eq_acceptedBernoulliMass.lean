-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:00:01.00933+00:00
-- url     : https://prove2.me/theorems/69a4951a-49b6-4162-928c-6cf9a303a20d
-- title:
--   HH18 Parameterized: decoded Instrument born Weight noisy Resources accepted eq accepted Bernoulli Mass
-- statement:
--   The noisy accepted decoded branch has exactly the existing accepted
--   Bernoulli mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L199-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L199-L206

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
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
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedInstrumentClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (decodedInstrument h hdegree).bornWeight .accepted
        (prepareMeasuredResources m w (noisyResources m w epsilon)) =
      acceptedBernoulliMass w r m epsilon := by sorry
