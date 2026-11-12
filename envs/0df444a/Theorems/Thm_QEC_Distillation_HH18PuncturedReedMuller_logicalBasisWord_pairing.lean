-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalBasisWord_pairing
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:51.094442+00:00
-- url     : https://prove2.me/theorems/df2ecd1d-e733-4514-9ef7-e5ed666b5d9b
-- title:
--   HH18 Punctured Reed Muller: logical Basis Word pairing
-- statement:
--   Systematic logical basis representatives have the source-stated delta
--   pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L868-L878
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L868-L878

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_pairing {w r m : Nat}
    (h : Admissible w r m) (left right : LogicalSite m w) :
    wordPairing (logicalBasisWord h left) (logicalBasisWord h right) =
      if left = right then 1 else 0 := by sorry
