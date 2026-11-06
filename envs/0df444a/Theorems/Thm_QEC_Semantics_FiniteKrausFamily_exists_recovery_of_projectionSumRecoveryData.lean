-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_recovery_of_projectionSumRecoveryData
-- name    : QEC.Semantics.FiniteKrausFamily.exists_recovery_of_projectionSumRecoveryData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:17.577467+00:00
-- url     : https://prove2.me/theorems/7a31b4d1-1dca-4e39-90f3-63a682fa116d
-- title:
--   Finite Kraus Family: exists recovery of projection Sum Recovery Data
-- statement:
--   Projection-sum recovery builder.
--
--   If a finite family of raw recovery Kraus operators has adjoint-square sum `S`,
--   `S` is an orthogonal projection, the finite recovery branches correct the
--   noise on code-supported density operators, and the residual branch `1 - S`
--   kills those same noisy states, then adding the residual branch packages the
--   data into a CPTP recovery channel.
--
--   This theorem is the final packaging/calculation layer below the full
--   Knill-Laflamme recovery construction.  It still requires separate mathematics
--   to produce the recovery Kraus operators from the KL scalar data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1476-L1532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1476-L1532

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

theorem QEC.Semantics.FiniteKrausFamily.exists_recovery_of_projectionSumRecoveryData
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (R : κ → KrausOperator H H)
    (S : Operator H)
    (hS_sum : S = ∑ a : κ, (LinearMap.adjoint (R a)).comp (R a))
    (hS_adjoint : LinearMap.adjoint S = S)
    (hS_idempotent : S.comp S = S)
    (hbranches : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ a : κ, (R a).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R a)))) =
          rho.toOperator)
    (hresidual : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (1 - S).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (1 - S))) = 0) :
    ∃ recovery : QuantumChannel H H,
      FiniteKrausCorrectable ι H H C E recovery := by sorry
