-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexMix_operator_adjoint
-- name    : QEC.Semantics.FiniteKrausFamily.indexMix_operator_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:35:53.573803+00:00
-- url     : https://prove2.me/theorems/3f252050-d990-42d2-98ac-bfaf5d67a260
-- title:
--   Finite Kraus Family: index Mix operator adjoint
-- statement:
--   The Finite Kraus Family construction uses the index Mix operator adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L549-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L549-L553

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

theorem QEC.Semantics.FiniteKrausFamily.indexMix_operator_adjoint (E : FiniteKrausFamily ι H H)
    (U : Matrix ι ι Complex) (a : ι) :
    LinearMap.adjoint ((E.indexMix U).operator a) =
      ∑ i : ι, star (U i a) • LinearMap.adjoint (E.operator i) := by sorry
