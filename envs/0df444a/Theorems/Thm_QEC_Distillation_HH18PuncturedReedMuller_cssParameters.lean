-- Prove2me | Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssParameters
-- name    : QEC.Distillation.HH18PuncturedReedMuller.cssParameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:29:36.462738+00:00
-- url     : https://prove2.me/theorems/1c2ed92d-0949-408d-8c3f-522a23f3ad21
-- title:
--   HH18 Punctured Reed Muller: css Parameters
-- statement:
--   Finite CSS parameters and the already-proved common semantic distance,
--   all packaged for the actual HH18 code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L973-L981
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean#L973-L981

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

theorem QEC.Distillation.HH18PuncturedReedMuller.cssParameters {w r m : Nat} (h : Admissible w r m) :
    Length (ZMod 2) (PhysicalSite m w) = binomialTail m w ∧
      Length (ZMod 2) (PhysicalSite m w) - Dimension (xCode w r m) -
          Dimension (zCode w r m) = binomialUpTo m w ∧
        Module.finrank Complex (cssCode h).stabilizer.code.carrier =
          2 ^ binomialUpTo m w ∧
        StabilizerCode.SemanticStabilizerDistance (sourceValidStabilizer h)
          (binomialTail (r + 1) w) := by sorry
