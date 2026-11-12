-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_tResourceAxis_transport
-- name    : QEC.Distillation.OneQubitMagic.phaseGate_tResourceAxis_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:10:57.685626+00:00
-- url     : https://prove2.me/theorems/123b2387-9800-4530-991a-9bb3fb71ba21
-- title:
--   One Qubit Magic: phase Gate t Resource Axis transport
-- statement:
--   Clifford phase conjugation rotates the word's axis from the `x-z` plane to `y-z`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L179-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TPhaseGeneratedUniversality.lean#L179-L193

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality

theorem QEC.Distillation.OneQubitMagic.phaseGate_tResourceAxis_transport :
    (phaseGate : SingleQubitMatrix) * axisPauliMatrix tResourceAxis *
        (((phaseGate⁻¹ : SingleQubitGate) : SingleQubitMatrix)) =
      axisPauliMatrix tResourceConjugateAxis := by sorry
