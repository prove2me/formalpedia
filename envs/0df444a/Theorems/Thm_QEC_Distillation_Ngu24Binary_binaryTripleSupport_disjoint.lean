-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTripleSupport_disjoint
-- name    : QEC.Distillation.Ngu24Binary.binaryTripleSupport_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:11:59.287845+00:00
-- url     : https://prove2.me/theorems/21334aa1-bcd9-42bf-9874-6115a84bcdf3
-- title:
--   Ngu24 Binary: binary Triple Support disjoint
-- statement:
--   The Ngu24 Binary construction uses the binary Triple Support disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L60-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L60-L75

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
variable [Fintype J]

theorem QEC.Distillation.Ngu24Binary.binaryTripleSupport_disjoint {x y : J × Fin 512} (hne : x ≠ y) :
    Disjoint (binaryTripleSupport J x) (binaryTripleSupport J y) := by sorry
