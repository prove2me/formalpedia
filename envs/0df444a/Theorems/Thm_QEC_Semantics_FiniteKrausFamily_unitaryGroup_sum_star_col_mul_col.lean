-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_unitaryGroup_sum_star_col_mul_col
-- name    : QEC.Semantics.FiniteKrausFamily.unitaryGroup_sum_star_col_mul_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:16:39.9152+00:00
-- url     : https://prove2.me/theorems/e3e43e62-9d68-4e8c-9de3-81f748770515
-- title:
--   Finite Kraus Family: unitary Group sum star col mul col
-- statement:
--   The Finite Kraus Family construction uses the unitary Group sum star col mul col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L561-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L561-L588

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

theorem QEC.Semantics.FiniteKrausFamily.unitaryGroup_sum_star_col_mul_col
    (U : Matrix.unitaryGroup ι Complex) (i j : ι) :
    (∑ a : ι,
      star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) =
      if i = j then 1 else 0 := by sorry
