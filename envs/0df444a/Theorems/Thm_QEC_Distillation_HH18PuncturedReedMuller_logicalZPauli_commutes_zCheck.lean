-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalZPauli_commutes_zCheck
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalZPauli_commutes_zCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:29:36.870693+00:00
-- url     : https://prove2.me/theorems/55db4559-c2ee-4aab-8b1b-e7a115b500f8
-- title:
--   HH18 Punctured Reed Muller: logical ZPauli commutes z Check
-- statement:
--   A logical `Z` representative commutes with every Z-type stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L912-L917
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L912-L917

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalZPauli_commutes_zCheck {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w)
    {z : Word (ZMod 2) (PhysicalSite m w)}
    (_hz : z ∈ (zCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalZPauli h logical) (cssZCheck z) := by sorry
