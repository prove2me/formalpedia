-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_hh18_15_1_0_parameters
-- name    : QEC.Distillation.HH18NoisyInput.hh18_15_1_0_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:52:38.410087+00:00
-- url     : https://prove2.me/theorems/546fe516-5ec6-4043-8719-d32c29cce72c
-- title:
--   HH18 Noisy Input: hh18 15 1 0 parameters
-- statement:
--   The consumed #759 construction really supplies the `[[15,1,3]]` carrier,
--   not an input-supplied code parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L310-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L310-L326

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18NoisyInput.hh18_15_1_0_parameters :
    Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite 4 0) = 15 ∧
      Length (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite 4 0) -
          Dimension (HH18PuncturedReedMuller.xCode 0 1 4) -
          Dimension (HH18PuncturedReedMuller.zCode 0 1 4) = 1 ∧
        Module.finrank Complex
            (HH18PuncturedReedMuller.cssCode hh18_15_1_0_admissible).stabilizer.code.carrier =
              2 ∧
          StabilizerCode.SemanticStabilizerDistance
            (HH18PuncturedReedMuller.sourceValidStabilizer
              hh18_15_1_0_admissible) 3 := by sorry
