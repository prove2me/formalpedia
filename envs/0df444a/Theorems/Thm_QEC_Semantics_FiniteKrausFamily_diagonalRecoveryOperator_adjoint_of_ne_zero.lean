-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_diagonalRecoveryOperator_adjoint_of_ne_zero
-- name    : QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_adjoint_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:46:34.502347+00:00
-- url     : https://prove2.me/theorems/1b01a0bd-f23b-4f23-a3f4-f6991b91491b
-- title:
--   Finite Kraus Family: diagonal Recovery Operator adjoint of ne zero
-- statement:
--   The Finite Kraus Family construction uses the diagonal Recovery Operator adjoint of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1069-L1092
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1069-L1092

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

theorem QEC.Semantics.FiniteKrausFamily.diagonalRecoveryOperator_adjoint_of_ne_zero
    {F : FiniteKrausFamily ι H H} {C : QuantumCode H} {lambda : ι → ℝ}
    {a : ι} (ha : lambda a ≠ 0) :
    LinearMap.adjoint (diagonalRecoveryOperator C F lambda a) =
      ((Real.sqrt (lambda a) : Complex)⁻¹) •
        (F.operator a).comp C.projector := by sorry
