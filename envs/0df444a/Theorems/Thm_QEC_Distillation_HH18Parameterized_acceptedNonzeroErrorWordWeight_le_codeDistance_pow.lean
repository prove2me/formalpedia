-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedNonzeroErrorWordWeight_le_codeDistance_pow
-- name    : QEC.Distillation.HH18Parameterized.acceptedNonzeroErrorWordWeight_le_codeDistance_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:03:11.95322+00:00
-- url     : https://prove2.me/theorems/1fb94f03-d92a-462f-bb37-dd85a78c0b4f
-- title:
--   HH18 Parameterized: accepted Nonzero Error Word Weight le code Distance pow
-- statement:
--   Every accepted nonzero physical word is bounded by the error monomial at
--   the actual constructed parameterized code distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L153-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L153-L159

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.acceptedNonzeroErrorWordWeight_le_codeDistance_pow {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (error : PhysicalErrorWord m w)
    (hresidual : Accepts w r m error ∧ error ≠ 0) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ codeDistance r w := by sorry
