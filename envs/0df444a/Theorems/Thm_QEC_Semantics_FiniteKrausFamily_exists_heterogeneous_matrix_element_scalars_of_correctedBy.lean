-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_exists_heterogeneous_matrix_element_scalars_of_correctedBy
-- name    : QEC.Semantics.FiniteKrausFamily.exists_heterogeneous_matrix_element_scalars_of_correctedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:10.110198+00:00
-- url     : https://prove2.me/theorems/90aea379-b6fe-4f95-b63f-24dc76eeb48f
-- title:
--   Finite Kraus Family: exists heterogeneous matrix element scalars of corrected By
-- statement:
--   Exact correction polarizes to scalar overlap equations for a heterogeneous noise family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L150-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L150-L195

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

theorem QEC.Semantics.FiniteKrausFamily.exists_heterogeneous_matrix_element_scalars_of_correctedBy
    (E : FiniteKrausFamily ι H K) (C : QuantumCode H)
    (R : κ → K →ₗ[Complex] H)
    (hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
          rho.toOperator) :
    ∃ scalar : ι → ι → Complex,
      ∀ i j (x : H), x ∈ C.carrier → ∀ y : H, y ∈ C.carrier →
        inner Complex (E.operator i x) (E.operator j y) =
          scalar i j * inner Complex x y := by sorry
