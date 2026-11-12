-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssLength
-- name    : QEC.Distillation.HH18PuncturedReedMuller.cssLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:52:05.771725+00:00
-- url     : https://prove2.me/theorems/97846e0c-6e90-4928-bdc0-62503545fab8
-- title:
--   HH18 Punctured Reed Muller: css Length
-- statement:
--   The exact number of retained HH18 physical coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L941-L943
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L941-L943

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

theorem QEC.Distillation.HH18PuncturedReedMuller.cssLength {w r m : Nat} (_h : Admissible w r m) :
    Length (ZMod 2) (PhysicalSite m w) = binomialTail m w := by sorry
