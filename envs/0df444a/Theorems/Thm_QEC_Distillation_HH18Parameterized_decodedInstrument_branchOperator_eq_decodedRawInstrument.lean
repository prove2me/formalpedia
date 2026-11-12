-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedInstrument_branchOperator_eq_decodedRawInstrument
-- name    : QEC.Distillation.HH18Parameterized.decodedInstrument_branchOperator_eq_decodedRawInstrument
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:08:43.259918+00:00
-- url     : https://prove2.me/theorems/04ba9ec1-044b-4f30-8c4d-fb638db2c0a4
-- title:
--   HH18 Parameterized: decoded Instrument branch Operator eq decoded Raw Instrument
-- statement:
--   Coarsening away the two unit observations changes no decoded branch
--   operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L28-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedInstrumentConditional.lean#L28-L39

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

theorem QEC.Distillation.HH18Parameterized.decodedInstrument_branchOperator_eq_decodedRawInstrument
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (decodedInstrument h hdegree).branchOperator outcome A =
      (decodedRawInstrument h hdegree).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A := by sorry
