-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryProjectionTerm_adjoint
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionTerm_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:17:54.60346+00:00
-- url     : https://prove2.me/theorems/b5785061-2b88-4146-89d4-3da813875ae0
-- title:
--   Finite Kraus Family: diagonal Recovery Projection Term adjoint
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Projection Term adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1211-L1219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1211-L1219

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryProjectionTerm_adjoint
    (F : FiniteKrausFamily ι H H) (C : QuantumCode H) (lambda : ι → ℝ)
    (a : ι) :
    LinearMap.adjoint
        ((LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
          (diagonalRecoveryOperator C F lambda a)) =
      (LinearMap.adjoint (diagonalRecoveryOperator C F lambda a)).comp
        (diagonalRecoveryOperator C F lambda a) := by sorry
