-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_cliffordPhaseGenerators_inverse_mem
-- name    : QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_inverse_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:57:26.128132+00:00
-- url     : https://prove2.me/theorems/cae1afbb-99a0-4e46-970a-eb6f63a43714
-- title:
--   One Qubit Magic: clifford Phase Generators inverse mem
-- statement:
--   Generated concrete gates are closed under inversion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L226-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L226-L230

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_inverse_mem (theta : Real)
    {U : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U⁻¹ ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) := by sorry
