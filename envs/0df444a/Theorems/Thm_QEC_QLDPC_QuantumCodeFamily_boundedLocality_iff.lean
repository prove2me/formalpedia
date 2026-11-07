-- Prove2me | Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_boundedLocality_iff
-- name    : QEC.QLDPC.QuantumCodeFamily.boundedLocality_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:59.039206+00:00
-- url     : https://prove2.me/theorems/3e6dae3f-91ef-4bfe-8ddb-531329d70da3
-- title:
--   Quantum Code Family: bounded Locality iff
-- statement:
--   A bound on both derived locality components is exactly bounded locality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L110-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/QuantumCodeFamily.lean#L110-L113

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
open QEC.QLDPC.QuantumCodeFamily
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.QuantumCodeFamily.boundedLocality_iff (F : QuantumCodeFamily A ι κ) (a : A) (bound : Nat) :
    Coding.BoundedLocality (F.localityProfile a) bound ↔
      F.maxCheckWeight a ≤ bound ∧ F.maxVariableDegree a ≤ bound := by sorry
