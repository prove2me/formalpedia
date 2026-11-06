-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_branch_scalar_of_finiteKraus_correctedBy
-- name    : QEC.Semantics.FiniteKrausFamily.exists_recovery_branch_scalar_of_finiteKraus_correctedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:16:14.809059+00:00
-- url     : https://prove2.me/theorems/b18e72c5-ebe9-48b5-b838-a230931f7efd
-- title:
--   Finite Kraus Family: exists recovery branch scalar of finite Kraus corrected By
-- statement:
--   KL96 `theorem:linear` bridge for the project finite-Kraus recovery semantics:
--   exact correction of code-supported density operators by finite recovery
--   branches forces each composite branch `R_r E_i` to be scalar on the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L469-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L469-L490

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

theorem QEC.Semantics.FiniteKrausFamily.exists_recovery_branch_scalar_of_finiteKraus_correctedBy
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (_hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
        rho.toOperator) :
    ∃ branchScalar : κ → ι → Complex,
      ∀ r i (x : H), x ∈ C.carrier →
        R r (E.operator i x) = branchScalar r i • x := by sorry
