-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalXPauli_commutes_logicalZPauli_iff
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalXPauli_commutes_logicalZPauli_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:30:07.730936+00:00
-- url     : https://prove2.me/theorems/950d778d-4ee9-44c3-8cda-abdeb155df88
-- title:
--   HH18 Punctured Reed Muller: logical XPauli commutes logical ZPauli iff
-- statement:
--   The chosen logical Pauli representatives commute precisely off the
--   logical-basis diagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L930-L938
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L930-L938

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalXPauli_commutes_logicalZPauli_iff

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalXPauli_commutes_logicalZPauli_iff {w r m : Nat}
    (h : Admissible w r m) (left right : LogicalSite m w) :
    PauliSymplectic.Commutes (logicalXPauli h left) (logicalZPauli h right) ↔
      left ≠ right := by sorry
