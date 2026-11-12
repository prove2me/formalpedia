-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_physicalErrorWords_card
-- name    : QEC.Distillation.HH18Parameterized.physicalErrorWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:48:20.39121+00:00
-- url     : https://prove2.me/theorems/444f48b8-18f6-4e66-8722-ab527b36b2c9
-- title:
--   HH18 Parameterized: physical Error Words card
-- statement:
--   The HH18 Parameterized construction uses the physical Error Words card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L140-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/ResourceMeasurement.lean#L140-L142

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.physicalErrorWords_card (m w : Nat) :
    (physicalErrorWords m w).card = Fintype.card (PhysicalErrorWord m w) := by sorry
