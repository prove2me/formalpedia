-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.postselectionInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:42:47.377172+00:00
-- url     : https://prove2.me/theorems/45fd98be-3cb8-4e30-a332-9e2d0c2c4ad0
-- title:
--   HH18 Parameterized: postselection Instrument complete
-- statement:
--   Coarse-graining retains completeness of the real finite joint-projector
--   Kraus family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L62-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L62-L64

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

theorem QEC.Distillation.HH18Parameterized.postselectionInstrument_complete {w r m : Nat} (h : Admissible w r m) :
    (postselectionInstrument h).kraus.Complete := by sorry
