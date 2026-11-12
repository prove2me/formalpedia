-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_fullSyndromeInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.fullSyndromeInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:58:14.798285+00:00
-- url     : https://prove2.me/theorems/dc2917cb-393c-445f-aca0-a8aeb7c9da9f
-- title:
--   HH18 Parameterized: full Syndrome Instrument complete
-- statement:
--   Completeness is derived from the actual finite joint-projector resolution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L113-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L113-L117

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

theorem QEC.Distillation.HH18Parameterized.fullSyndromeInstrument_complete {w r m : Nat} (h : Admissible w r m) :
    (fullSyndromeInstrument h).kraus.Complete := by sorry
