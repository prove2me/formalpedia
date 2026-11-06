-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_cross
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:17:24.574465+00:00
-- url     : https://prove2.me/theorems/515790e0-c635-4456-a397-ad212850a6d2
-- title:
--   Finite Kraus Family: diagonal Recovery Operator cross
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Operator cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1094-L1148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1094-L1148

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_cross
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (a b : ι) :
    (diagonalRecoveryOperator C F lambda a).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda b)) =
      if a = b then
        if lambda a = 0 then 0 else C.projector
      else 0 := by sorry
