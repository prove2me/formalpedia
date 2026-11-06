-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_branches
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_branches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:08.1302+00:00
-- url     : https://prove2.me/theorems/799ff04f-d929-463d-b9d5-0bdf1cf8d418
-- title:
--   Finite Kraus Family: diagonal Recovery Operator branches
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Operator branches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1270-L1317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1270-L1317

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_branches
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    (hlambda_nonneg : ∀ i : ι, 0 ≤ lambda i)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar F C
      (fun i j : ι => Matrix.diagonal (fun k : ι => (lambda k : Complex)) i j))
    (hdiag_sum : (∑ i : ι, (lambda i : Complex)) • C.projector = C.projector)
    (rho : DensityOperator H) (hρ : DensityOperator.SupportedOn C rho) :
    (∑ a : ι, (diagonalRecoveryOperator C F lambda a).comp
      ((F.inducedMap rho.toOperator).comp
        (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)))) =
      rho.toOperator := by sorry
