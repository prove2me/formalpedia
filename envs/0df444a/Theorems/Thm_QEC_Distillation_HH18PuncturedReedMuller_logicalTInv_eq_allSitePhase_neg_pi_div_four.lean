-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalTInv_eq_allSitePhase_neg_pi_div_four
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalTInv_eq_allSitePhase_neg_pi_div_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:39:50.630888+00:00
-- url     : https://prove2.me/theorems/79213fdb-9108-42d0-9a26-4618061b99cd
-- title:
--   HH18 Punctured Reed Muller: logical TInv eq all Site Phase neg pi div four
-- statement:
--   The named HH18 logical inverse-`T` is the negative `π/4` all-site phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L1203-L1208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L1203-L1208

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalTInv_eq_allSitePhase_neg_pi_div_four (w m : Nat) :
    logicalTInv w m =
      Triorthogonal.allSitePhase (Index := LogicalSite m w) (-Real.pi / 4) := by sorry
