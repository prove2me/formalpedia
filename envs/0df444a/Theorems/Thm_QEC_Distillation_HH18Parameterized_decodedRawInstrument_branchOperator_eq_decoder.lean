-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRawInstrument_branchOperator_eq_decoder
-- name    : QEC.Distillation.HH18Parameterized.decodedRawInstrument_branchOperator_eq_decoder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:08:55.610245+00:00
-- url     : https://prove2.me/theorems/099a2a3a-24dc-45e8-9bad-4ab1f9910de4
-- title:
--   HH18 Parameterized: decoded Raw Instrument branch Operator eq decoder
-- statement:
--   The decoded raw branch is the actual decoder channel applied to the
--   retained physical resource/postselection branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L43-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L43-L56

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
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

theorem QEC.Distillation.HH18Parameterized.decodedRawInstrument_branchOperator_eq_decoder
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (decodedRawInstrument h hdegree).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A =
      decoderChannel h
        ((resourcePostselectionInstrument h hdegree).branchOperator
          ⟨PUnit.unit, outcome⟩ A) := by sorry
