-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge
-- name    : QEC.Distillation.HH18Parameterized.errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:03:06.360529+00:00
-- url     : https://prove2.me/theorems/63ffe5e9-e51e-4c31-8a98-04b07bd11f62
-- title:
--   HH18 Parameterized: error Word Weight le code Distance pow of hamming Weight ge
-- statement:
--   The actual Bernoulli weight of a word whose Hamming weight is at least the
--   parameterized code distance is at most the matching error monomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L129-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean#L129-L149

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

theorem QEC.Distillation.HH18Parameterized.errorWordWeight_le_codeDistance_pow_of_hammingWeight_ge {w r m : Nat}
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord m w)
    (hweight : codeDistance r w ≤ HammingWeight error) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ codeDistance r w := by sorry
