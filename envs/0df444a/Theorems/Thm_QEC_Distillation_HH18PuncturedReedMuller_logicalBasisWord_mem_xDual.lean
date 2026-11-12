-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalBasisWord_mem_xDual
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_mem_xDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:40.653313+00:00
-- url     : https://prove2.me/theorems/6ff566ce-c6cb-451b-bfdd-377bffd8fa39
-- title:
--   HH18 Punctured Reed Muller: logical Basis Word mem x Dual
-- statement:
--   Each systematic logical basis word is dual to the actual X checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L822-L864
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L822-L864

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_mem_xDual {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    logicalBasisWord h logical ∈ (xCode w r m).dual.carrier := by sorry
