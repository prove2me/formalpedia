-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_idempotent
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:11.47077+00:00
-- url     : https://prove2.me/theorems/4329f123-a957-4075-aa0d-4e55998a97ed
-- title:
--   Finite Kraus Family: diagonal Recovery Projection Sum idempotent
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Projection Sum idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1236-L1268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1236-L1268

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_idempotent
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j)) :
    (∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a)).comp
      (∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)) =
    ∑ a : ι,
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a) := by sorry
