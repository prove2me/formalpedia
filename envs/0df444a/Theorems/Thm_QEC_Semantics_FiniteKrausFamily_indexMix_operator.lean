-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexMix_operator
-- name    : QEC.Semantics.FiniteKrausFamily.indexMix_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:35:12.303028+00:00
-- url     : https://prove2.me/theorems/ea228c64-fe63-47f5-a2e4-f81fe6852dd5
-- title:
--   Finite Kraus Family: index Mix operator
-- statement:
--   The Finite Kraus Family construction uses the index Mix operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L543-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L543-L546

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
omit [DecidableEq ι]

theorem QEC.Semantics.FiniteKrausFamily.indexMix_operator (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    (E.indexMix U).operator a = ∑ i : ι, U i a • E.operator i := by sorry
