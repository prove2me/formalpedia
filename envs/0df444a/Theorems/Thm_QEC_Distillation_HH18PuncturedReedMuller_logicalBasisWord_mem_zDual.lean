-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalBasisWord_mem_zDual
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_mem_zDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:22.204192+00:00
-- url     : https://prove2.me/theorems/5e437a32-6985-4bb1-8a1c-0bf6370463ba
-- title:
--   HH18 Punctured Reed Muller: logical Basis Word mem z Dual
-- statement:
--   Each systematic logical basis word is in the actual Z normalizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L813-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L813-L819

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalBasisWord_mem_zDual {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    logicalBasisWord h logical ∈ (zCode w r m).dual.carrier := by sorry
