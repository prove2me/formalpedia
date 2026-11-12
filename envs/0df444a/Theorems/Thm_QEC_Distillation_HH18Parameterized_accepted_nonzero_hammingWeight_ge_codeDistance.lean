-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_accepted_nonzero_hammingWeight_ge_codeDistance
-- name    : QEC.Distillation.HH18Parameterized.accepted_nonzero_hammingWeight_ge_codeDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:58:43.4662+00:00
-- url     : https://prove2.me/theorems/1291bd4b-1e05-4406-86b1-bf059e1d8321
-- title:
--   HH18 Parameterized: accepted nonzero hamming Weight ge code Distance
-- statement:
--   Every nonzero accepted diagonal-error word has weight at least the actual
--   distance derived from the constructed parameterized `xCode`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L415-L422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L415-L422

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

theorem QEC.Distillation.HH18Parameterized.accepted_nonzero_hammingWeight_ge_codeDistance {w r m : Nat}
    (h : Admissible w r m) (error : PhysicalErrorWord m w)
    (herror : error ≠ 0) (haccept : Accepts w r m error) :
    codeDistance r w ≤ HammingWeight error := by sorry
