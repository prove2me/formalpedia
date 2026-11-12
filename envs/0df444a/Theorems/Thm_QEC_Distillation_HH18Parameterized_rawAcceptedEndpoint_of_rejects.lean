-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_rawAcceptedEndpoint_of_rejects
-- name    : QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_of_rejects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:38.840646+00:00
-- url     : https://prove2.me/theorems/0b91fa1c-e0ce-4da8-b3b8-b3a76b66dacb
-- title:
--   HH18 Parameterized: raw Accepted Endpoint of rejects
-- statement:
--   A rejected physical-error word has a literal zero accepted raw endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L215-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Postselection.lean#L215-L220

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

theorem QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_of_rejects {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (hreject : ¬ Accepts w r m error) :
    rawAcceptedEndpoint h error outcomes = 0 := by sorry
