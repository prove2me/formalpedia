-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssCarrierFinrank
-- name    : QEC.Distillation.HH18PuncturedReedMuller.cssCarrierFinrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:52:25.892868+00:00
-- url     : https://prove2.me/theorems/c8ad5dcc-e25e-4206-be1a-99b0681a42a7
-- title:
--   HH18 Punctured Reed Muller: css Carrier Finrank
-- statement:
--   The actual CSS carrier has the expected finite logical dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L962-L969
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L962-L969

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

theorem QEC.Distillation.HH18PuncturedReedMuller.cssCarrierFinrank {w r m : Nat} (h : Admissible w r m) :
    Module.finrank Complex (cssCode h).stabilizer.code.carrier =
      2 ^ binomialUpTo m w := by sorry
