-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_resourceDecodedRun_operation
-- name    : QEC.Distillation.HH18Parameterized.resourceDecodedRun_operation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:08:30.270782+00:00
-- url     : https://prove2.me/theorems/936bdb76-d7aa-4356-baad-79e9457fbe68
-- title:
--   HH18 Parameterized: resource Decoded Run operation
-- statement:
--   The HH18 Parameterized construction uses the resource Decoded Run operation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/NormalizedRun.lean#L180-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/NormalizedRun.lean#L180-L184

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instNormalizedRunClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.resourceDecodedRun_operation {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (resourceDecodedRun h hdegree inputs).operation = decodedOperation h hdegree := by sorry
