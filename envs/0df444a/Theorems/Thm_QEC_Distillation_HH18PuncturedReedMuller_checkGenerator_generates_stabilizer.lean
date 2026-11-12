-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_checkGenerator_generates_stabilizer
-- name    : QEC.Distillation.HH18PuncturedReedMuller.checkGenerator_generates_stabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:27:44.661209+00:00
-- url     : https://prove2.me/theorems/7e1787a1-7d3b-4989-aa23-d479ff5b9b16
-- title:
--   HH18 Punctured Reed Muller: check Generator generates stabilizer
-- statement:
--   The chosen finite family generates the stabilizer's actual generated group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L241-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L241-L247

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18PuncturedReedMuller.checkGenerator_generates_stabilizer {w r m : Nat}
    (h : Admissible w r m) :
    generatedStabilizerSet (checkGenerator w r m) =
      (stabilizer h).generatedGroup := by sorry
