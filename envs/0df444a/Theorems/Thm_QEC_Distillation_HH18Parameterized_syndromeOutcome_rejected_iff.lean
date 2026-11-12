-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_syndromeOutcome_rejected_iff
-- name    : QEC.Distillation.HH18Parameterized.syndromeOutcome_rejected_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:37:32.086763+00:00
-- url     : https://prove2.me/theorems/18dfe595-101d-4cf9-86e4-73ffc5c42d0a
-- title:
--   HH18 Parameterized: syndrome Outcome rejected iff
-- statement:
--   The coarse rejected outcome is exactly every non-all-positive syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L47-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L47-L50

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
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

theorem QEC.Distillation.HH18Parameterized.syndromeOutcome_rejected_iff (w r m : Nat) (syndrome : Syndrome w r m) :
    syndromeOutcome w r m syndrome = .rejected ↔
      syndrome ≠ HH18PuncturedReedMuller.allPositiveSyndrome w r m := by sorry
