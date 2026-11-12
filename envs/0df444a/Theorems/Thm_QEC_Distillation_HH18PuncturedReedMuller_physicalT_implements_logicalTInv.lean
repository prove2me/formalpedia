-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalT_implements_logicalTInv
-- name    : QEC.Distillation.HH18PuncturedReedMuller.physicalT_implements_logicalTInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:29:44.829935+00:00
-- url     : https://prove2.me/theorems/10fa2c1a-8baa-43ee-add7-906d2376b95f
-- title:
--   HH18 Punctured Reed Muller: physical T implements logical TInv
-- statement:
--   Simultaneous physical `T` implements simultaneous logical `T†` on HH18.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L1211-L1216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L1211-L1216

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

theorem QEC.Distillation.HH18PuncturedReedMuller.physicalT_implements_logicalTInv {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (encodedCode h).ImplementsLogicalGate (physicalT w m) (logicalTInv w m) := by sorry
