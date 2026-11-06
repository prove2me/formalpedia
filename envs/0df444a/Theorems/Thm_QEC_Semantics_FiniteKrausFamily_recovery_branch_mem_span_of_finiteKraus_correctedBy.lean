-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_recovery_branch_mem_span_of_finiteKraus_correctedBy
-- name    : QEC.Semantics.FiniteKrausFamily.recovery_branch_mem_span_of_finiteKraus_correctedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:16:29.071184+00:00
-- url     : https://prove2.me/theorems/f6794657-4f3c-4878-ba78-d9889623ccc1
-- title:
--   Finite Kraus Family: recovery branch mem span of finite Kraus corrected By
-- statement:
--   For a pure code state recovered exactly by finite Kraus branches, each composite
--   branch vector lies in the span of the input code vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L373-L462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L373-L462

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

theorem QEC.Semantics.FiniteKrausFamily.recovery_branch_mem_span_of_finiteKraus_correctedBy
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
        rho.toOperator)
    (r : κ) (i : ι) {x : H} (hxC : x ∈ C.carrier) :
    R r (E.operator i x) ∈ Complex ∙ x := by sorry
