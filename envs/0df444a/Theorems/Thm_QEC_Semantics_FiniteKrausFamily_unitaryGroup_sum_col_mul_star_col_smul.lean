-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_unitaryGroup_sum_col_mul_star_col_smul
-- name    : QEC.Semantics.FiniteKrausFamily.unitaryGroup_sum_col_mul_star_col_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:17:02.197202+00:00
-- url     : https://prove2.me/theorems/651890d6-fffe-45fd-bee2-046da40f666e
-- title:
--   Finite Kraus Family: unitary Group sum col mul star col smul
-- statement:
--   The Finite Kraus Family construction uses the unitary Group sum col mul star col smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L641-L679
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L641-L679

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

theorem QEC.Semantics.FiniteKrausFamily.unitaryGroup_sum_col_mul_star_col_smul
    {M : Type*} [AddCommMonoid M] [Module Complex M]
    (U : Matrix.unitaryGroup ι Complex) (B : ι → ι → M) :
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      ((U : Matrix ι ι Complex) i a *
        star ((U : Matrix ι ι Complex) j a)) • B i j) =
      ∑ i : ι, B i i := by sorry
