-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_detectable_of_card_lt_distance
-- name    : QEC.QLDPC.QuantumCodeFamily.detectable_of_card_lt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:12.78396+00:00
-- url     : https://prove2.me/theorems/e96eb871-0d1f-4bc6-9cbd-f5c9a98da1b4
-- title:
--   Quantum Code Family: detectable of card lt distance
-- statement:
--   Operators supported on fewer than the indexed distance are detectable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L84-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L84-L92

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_detectable_of_card_lt_distance

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.detectable_of_card_lt_distance
    (F : QuantumCodeFamily A ι κ) (a : A)
    (region : Semantics.QuditSubsystem
      (uniformQuditDimensions (ι := ι a) (F.presentation a).alphabetSize))
    (hcard : Fintype.card region.SelectedCoordinates < F.distance a)
    (localOperator : Semantics.Operator region.selectedSystem) :
    Semantics.DetectableOn (F.presentation a).code
      (region.extendLocalToRegister localOperator) := by sorry
