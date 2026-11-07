-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
-- name    : QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:50.73717+00:00
-- url     : https://prove2.me/theorems/718ea673-8fe3-4a48-9e72-bd63ea154d45
-- title:
--   Quantum Code Family: block Length eq card
-- statement:
--   Physical length counts the actual coordinates of the indexed register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L60-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L60-L62

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card (F : QuantumCodeFamily A ι κ) (a : A) :
    F.blockLength a = Fintype.card (ι a) := by sorry
