-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mem_generated
-- name    : QEC.Distillation.OneQubitMagic.phaseGate_mem_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:50:42.733737+00:00
-- url     : https://prove2.me/theorems/d253e5ce-583a-4cce-a1a2-bd2e1e7d373b
-- title:
--   One Qubit Magic: phase Gate mem generated
-- statement:
--   The One Qubit Magic construction uses the phase Gate mem generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L209-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L209-L211

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseGate_mem_generated (theta : Real) :
    phaseGate ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) := by sorry
