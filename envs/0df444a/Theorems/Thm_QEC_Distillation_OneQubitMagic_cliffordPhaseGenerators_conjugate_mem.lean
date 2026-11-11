-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_cliffordPhaseGenerators_conjugate_mem
-- name    : QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_conjugate_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T14:54:33.205406+00:00
-- url     : https://prove2.me/theorems/829c1569-fa28-42df-97cd-905ea6c3dec5
-- title:
--   One Qubit Magic: clifford Phase Generators conjugate mem
-- statement:
--   Generated concrete gates are closed under generated conjugation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L233-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean#L233-L238

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.cliffordPhaseGenerators_conjugate_mem (theta : Real)
    {U V : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta))
    (hV : V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U * V * U⁻¹ ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) := by sorry
