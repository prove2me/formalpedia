-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Postselection_syndromeOutcome_accepted_iff
-- name    : QEC.Distillation.HH18Postselection.syndromeOutcome_accepted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:49:17.183824+00:00
-- url     : https://prove2.me/theorems/cd3ca3a9-c153-4b5d-aca6-34e0b91695a6
-- title:
--   HH18 Postselection: syndrome Outcome accepted iff
-- statement:
--   The coarse accepted outcome is exactly the all-positive syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L41-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Postselection.lean#L41-L44

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

theorem QEC.Distillation.HH18Postselection.syndromeOutcome_accepted_iff (syndrome : Syndrome) :
    syndromeOutcome syndrome = .accepted ↔
      syndrome = HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 := by sorry
