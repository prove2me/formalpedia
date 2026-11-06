-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionSum_residual
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:15.261404+00:00
-- url     : https://prove2.me/theorems/6f6bbe98-4b86-44f8-ac61-1cd2aaded32d
-- title:
--   Finite Kraus Family: diagonal Recovery Projection Sum residual
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Projection Sum residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1396-L1459
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1396-L1459

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionSum_residual
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho) :
    let S : Operator H :=
      ∑ a : ι,
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)
    (1 - S).comp
      ((F.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) = 0 := by sorry
