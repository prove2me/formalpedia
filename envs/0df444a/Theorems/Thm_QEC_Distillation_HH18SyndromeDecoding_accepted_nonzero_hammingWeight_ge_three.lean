-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_accepted_nonzero_hammingWeight_ge_three
-- name    : QEC.Distillation.HH18SyndromeDecoding.accepted_nonzero_hammingWeight_ge_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:46:38.4519+00:00
-- url     : https://prove2.me/theorems/40ff6613-68ba-4fd2-8e36-2e5034a4e3c9
-- title:
--   HH18 Syndrome Decoding: accepted nonzero hamming Weight ge three
-- statement:
--   Every nonzero accepted HH18 diagonal-error word has physical weight at
--   least three.  This is the distance input for the cubic error recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L477-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L477-L482

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18SyndromeDecoding.accepted_nonzero_hammingWeight_ge_three (error : PhysicalErrorWord)
    (herror : error ≠ 0) (haccept : Accepts error) :
    3 ≤ HammingWeight error := by sorry
