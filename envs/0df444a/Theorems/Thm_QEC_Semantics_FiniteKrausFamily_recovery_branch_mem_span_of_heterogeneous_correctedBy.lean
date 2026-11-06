-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_recovery_branch_mem_span_of_heterogeneous_correctedBy
-- name    : QEC.Semantics.FiniteKrausFamily.recovery_branch_mem_span_of_heterogeneous_correctedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:04.862192+00:00
-- url     : https://prove2.me/theorems/b1a7b770-1fa5-4fcb-8fcb-252674ff7332
-- title:
--   Finite Kraus Family: recovery branch mem span of heterogeneous corrected By
-- statement:
--   For a heterogeneous finite Kraus noise family followed by finite recovery
--   branches, exact correction of every supported density forces every composite
--   branch to preserve the ray of each code vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L57-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L57-L147

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.FiniteKrausFamily
variable {H : Type u} {K : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [Fintype ι] [Fintype κ]

theorem QEC.Semantics.FiniteKrausFamily.recovery_branch_mem_span_of_heterogeneous_correctedBy
    (E : FiniteKrausFamily ι H K) (C : QuantumCode H)
    (R : κ → K →ₗ[Complex] H)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
          rho.toOperator)
    (r : κ) (i : ι) {x : H} (hxC : x ∈ C.carrier) :
    R r (E.operator i x) ∈ Complex ∙ x := by sorry
