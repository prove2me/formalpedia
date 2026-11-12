-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_syndromeOutcome_rejected_iff
-- name    : QEC.Distillation.HH18Postselection.syndromeOutcome_rejected_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:49:23.375637+00:00
-- url     : https://prove2.me/theorems/272956ad-0595-4167-8284-e379ec97dcc1
-- title:
--   HH18 Postselection: syndrome Outcome rejected iff
-- statement:
--   The coarse rejected outcome is exactly every non-all-positive syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L47-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L47-L50

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Postselection
open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Postselection.syndromeOutcome_rejected_iff (syndrome : Syndrome) :
    syndromeOutcome syndrome = .rejected ↔
      syndrome ≠ HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 := by sorry
