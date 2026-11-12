-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_codeDistance_semanticDistance
-- name    : QEC.Distillation.HH18Parameterized.codeDistance_semanticDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:34:57.882773+00:00
-- url     : https://prove2.me/theorems/8fedea49-8336-488e-8ae0-5bc35c879cd4
-- title:
--   HH18 Parameterized: code Distance semantic Distance
-- statement:
--   The named distance is attained by the actual source-valid parameterized
--   HH18 CSS stabilizer, rather than carried as detached protocol metadata.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L69-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean#L69-L72

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.codeDistance_semanticDistance {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode.SemanticStabilizerDistance
      (HH18PuncturedReedMuller.sourceValidStabilizer h) (codeDistance r w) := by sorry
