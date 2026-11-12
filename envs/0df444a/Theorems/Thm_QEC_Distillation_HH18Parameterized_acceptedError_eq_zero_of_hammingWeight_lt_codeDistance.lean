-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedError_eq_zero_of_hammingWeight_lt_codeDistance
-- name    : QEC.Distillation.HH18Parameterized.acceptedError_eq_zero_of_hammingWeight_lt_codeDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:58:56.16164+00:00
-- url     : https://prove2.me/theorems/0c119f1d-2327-4d7e-8fbb-66eaa8e39bf3
-- title:
--   HH18 Parameterized: accepted Error eq zero of hamming Weight lt code Distance
-- statement:
--   An accepted pure-Z error below the actual `xCode` dual distance is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L384-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L384-L411

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
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
universe u

theorem QEC.Distillation.HH18Parameterized.acceptedError_eq_zero_of_hammingWeight_lt_codeDistance {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (hweight : HammingWeight error < codeDistance r w)
    (haccept : Accepts w r m error) :
    error = 0 := by sorry
