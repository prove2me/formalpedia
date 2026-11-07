-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_localityProfile_eq_incidence
-- name    : QEC.QLDPC.QuantumCodeFamily.localityProfile_eq_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:12.856211+00:00
-- url     : https://prove2.me/theorems/e13d84c6-cf0e-474f-be7a-2da1f965120f
-- title:
--   Quantum Code Family: locality Profile eq incidence
-- statement:
--   Indexed locality is precisely the incidence profile of its actual checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L95-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L95-L97

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_localityProfile_eq_incidence

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.localityProfile_eq_incidence (F : QuantumCodeFamily A ι κ) (a : A) :
    F.localityProfile a = (F.presentation a).incidence.localityProfile := by sorry
