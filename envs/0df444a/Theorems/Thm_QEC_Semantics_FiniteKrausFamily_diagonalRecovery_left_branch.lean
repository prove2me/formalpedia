-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecovery_left_branch
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecovery_left_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:17:05.561081+00:00
-- url     : https://prove2.me/theorems/a4ffc375-54ad-4a25-8a27-3778b74358d5
-- title:
--   Finite Kraus Family: diagonal Recovery left branch
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery left branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L837-L900
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L837-L900

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecovery_left_branch
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a : {i : ι // lambda i ≠ 0}) (i : ι) :
    (((((Real.sqrt (lambda a.1) : Complex)⁻¹) •
        C.projector.comp (LinearMap.adjoint (F.operator a.1))).comp
        ((F.operator i).comp C.projector)) : Operator H) =
      if a.1 = i then (Real.sqrt (lambda a.1) : Complex) • C.projector else 0 := by sorry
