-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalT_eq_allSiteT
-- name    : QEC.Distillation.HH18PuncturedReedMuller.physicalT_eq_allSiteT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:39:47.772144+00:00
-- url     : https://prove2.me/theorems/1415681c-ac69-44be-adec-9a3ca2e63277
-- title:
--   HH18 Punctured Reed Muller: physical T eq all Site T
-- statement:
--   The named HH18 physical `T` is the generic raw all-site `T` transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L1197-L1200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L1197-L1200

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

theorem QEC.Distillation.HH18PuncturedReedMuller.physicalT_eq_allSiteT (w m : Nat) :
    physicalT w m = Triorthogonal.allSiteT (Index := PhysicalSite m w) := by sorry
