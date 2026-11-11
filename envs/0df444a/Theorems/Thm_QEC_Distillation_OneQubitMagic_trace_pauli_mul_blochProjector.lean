-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_trace_pauli_mul_blochProjector
-- name    : QEC.Distillation.OneQubitMagic.trace_pauli_mul_blochProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:05:05.911187+00:00
-- url     : https://prove2.me/theorems/c64435e4-a0e1-440f-90b5-7b4501827bab
-- title:
--   One Qubit Magic: trace pauli mul bloch Projector
-- statement:
--   The One Qubit Magic construction uses the trace pauli mul bloch Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L169-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L169-L179

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.trace_pauli_mul_blochProjector
    (r : PauliAxis -> Real) (i : PauliAxis) :
    LinearMap.trace Complex QubitSpace
      (pauliOperator i * blochProjector r) = r i := by sorry
