-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_density_branch
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_density_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:17:37.555364+00:00
-- url     : https://prove2.me/theorems/6386c143-49cf-4740-a74c-bcaf5364deef
-- title:
--   Finite Kraus Family: diagonal Recovery Operator density branch
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Operator density branch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L995-L1047
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L995-L1047

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_density_branch
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho)
    (a i : ι) :
    (diagonalRecoveryOperator C F lambda a).comp
        ((F.operator i).comp
          (rho.toOperator.comp
            ((LinearMap.adjoint (F.operator i)).comp
              (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a))))) =
      if a = i then (lambda i : Complex) • rho.toOperator else 0 := by sorry
