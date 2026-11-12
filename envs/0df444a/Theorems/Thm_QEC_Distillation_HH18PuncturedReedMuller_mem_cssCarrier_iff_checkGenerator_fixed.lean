-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_mem_cssCarrier_iff_checkGenerator_fixed
-- name    : QEC.Distillation.HH18PuncturedReedMuller.mem_cssCarrier_iff_checkGenerator_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:29:35.77043+00:00
-- url     : https://prove2.me/theorems/e10b54f0-59cf-49a2-a756-1f012a0eddd8
-- title:
--   HH18 Punctured Reed Muller: mem css Carrier iff check Generator fixed
-- statement:
--   Membership in the actual CSS carrier is finite basis-check fixedness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L365-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L365-L391

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

theorem QEC.Distillation.HH18PuncturedReedMuller.mem_cssCarrier_iff_checkGenerator_fixed {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (PhysicalSite m w)) :
    psi ∈ (cssCode h).stabilizer.code.carrier ↔
      ∀ check, toQubitOperator (checkGenerator w r m check) psi = psi := by sorry
