-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_cliffordPhaseGenerators_compose_mem
-- name    : QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_compose_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T16:13:14.322877+00:00
-- url     : https://prove2.me/theorems/38f17193-9d29-4beb-9e08-5d66286e576c
-- title:
--   One Qubit Magic: clifford Phase Generators compose mem
-- statement:
--   Generated concrete gates are closed under composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L218-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L218-L223

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_compose_mem (theta : Real)
    {U V : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta))
    (hV : V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U * V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) := by sorry
