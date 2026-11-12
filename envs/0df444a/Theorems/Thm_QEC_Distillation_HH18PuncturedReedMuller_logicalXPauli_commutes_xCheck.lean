-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_logicalXPauli_commutes_xCheck
-- name    : QEC.Distillation.HH18PuncturedReedMuller.logicalXPauli_commutes_xCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:29:15.715845+00:00
-- url     : https://prove2.me/theorems/b53aa21d-e47e-46d9-adfd-9519d98922f9
-- title:
--   HH18 Punctured Reed Muller: logical XPauli commutes x Check
-- statement:
--   A logical `X` representative commutes with every X-type stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L893-L898
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L893-L898

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

theorem QEC.Distillation.HH18PuncturedReedMuller.logicalXPauli_commutes_xCheck {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w)
    {x : Word (ZMod 2) (PhysicalSite m w)}
    (_hx : x ∈ (xCode w r m).carrier) :
    PauliSymplectic.Commutes (logicalXPauli h logical) (cssXCheck x) := by sorry
