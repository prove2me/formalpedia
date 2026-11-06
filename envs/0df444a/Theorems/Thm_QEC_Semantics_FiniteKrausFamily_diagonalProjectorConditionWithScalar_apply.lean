-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalProjectorConditionWithScalar_apply
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalProjectorConditionWithScalar_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:46:39.893357+00:00
-- url     : https://prove2.me/theorems/d869846e-0e6a-4b81-9715-4784607a0e98
-- title:
--   Finite Kraus Family: diagonal Projector Condition With Scalar apply
-- statement:
--   The Finite Kraus Family construction uses the diagonal Projector Condition With Scalar apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L827-L835
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L827-L835

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalProjectorConditionWithScalar_apply
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (i j : ι) :
    (C.projector.comp ((LinearMap.adjoint (F.operator i)).comp (F.operator j))).comp
        C.projector =
      (if i = j then (lambda i : Complex) else 0) • C.projector := by sorry
