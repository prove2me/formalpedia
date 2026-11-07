-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_distance_le_blockLength
-- name    : QEC.QLDPC.QuantumCodeFamily.distance_le_blockLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:46.519719+00:00
-- url     : https://prove2.me/theorems/3c32d51e-2695-437f-959f-eaa051840dcc
-- title:
--   Quantum Code Family: distance le block Length
-- statement:
--   Every indexed code has distance at most its actual physical length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L79-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L79-L81

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_le_blockLength

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.distance_le_blockLength (F : QuantumCodeFamily A ι κ) (a : A) :
    F.distance a ≤ F.blockLength a := by sorry
