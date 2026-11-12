-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_bornWeight_eq_decodedRawInstrument
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_eq_decodedRawInstrument
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:01:33.892326+00:00
-- url     : https://prove2.me/theorems/98b035ec-0ca9-43cc-b715-5024b4dec2f0
-- title:
--   HH18 Parameterized: decoded Instrument born Weight eq decoded Raw Instrument
-- statement:
--   Coarsening the two unit observations preserves the Born weight of each
--   real postselection outcome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L114-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrument.lean#L114-L127

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

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_bornWeight_eq_decodedRawInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (rho : DensityOperator (PhysicalRegister m w)) :
    (decodedInstrument h hdegree).bornWeight outcome rho =
      (decodedRawInstrument h hdegree).bornWeight
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ rho := by sorry
