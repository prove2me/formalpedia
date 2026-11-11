-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_pauliX
-- name    : QEC.Distillation.OneQubitMagic.hadamard_conj_pauliX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:58:56.290873+00:00
-- url     : https://prove2.me/theorems/c257e08b-d5fc-4e9f-9c8f-fe5eae9d096d
-- title:
--   One Qubit Magic: hadamard conj pauli X
-- statement:
--   Concrete `H X H⁻¹ = Z`, realizing the `hadamardClifford` X-to-Z action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean#L410-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean#L410-L416

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
noncomputable section

theorem QEC.Distillation.OneQubitMagic.hadamard_conj_pauliX :
    hadamardTransport.conjOperator pauliX = pauliZ := by sorry
