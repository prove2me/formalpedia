-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_operator_scalar_on_code_of_forall_mem_span
-- name    : QEC.Semantics.FiniteKrausFamily.operator_scalar_on_code_of_forall_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:45:36.886831+00:00
-- url     : https://prove2.me/theorems/4268f3a2-c58a-4b2f-9414-4fe1cc194ee9
-- title:
--   Finite Kraus Family: operator scalar on code of forall mem span
-- statement:
--   If a linear operator sends every code vector into its own one-dimensional span,
--   then it is scalar on the whole code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L326-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L326-L367

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.operator_scalar_on_code_of_forall_mem_span
    (A : Operator H) (C : QuantumCode H)
    (hline : ∀ (x : H), x ∈ C.carrier → A x ∈ Complex ∙ x) :
    ∃ scalar : Complex, ∀ (x : H), x ∈ C.carrier → A x = scalar • x := by sorry
