-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
-- name    : QEC.Semantics.FiniteKrausFamily.diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:17:09.030067+00:00
-- url     : https://prove2.me/theorems/bfb05648-e66f-4c36-9020-40913fca906b
-- title:
--   Finite Kraus Family: diagonal error comp projector eq zero of lambda eq zero
-- statement:
--   The Finite Kraus Family construction uses the diagonal error comp projector eq zero of lambda eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L902-L928
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L902-L928

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
variable [DecidableEq ι]

theorem QEC.Semantics.FiniteKrausFamily.diagonal_error_comp_projector_eq_zero_of_lambda_eq_zero
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    {i : ι} (hzero : lambda i = 0) :
    (F.operator i).comp C.projector = 0 := by sorry
