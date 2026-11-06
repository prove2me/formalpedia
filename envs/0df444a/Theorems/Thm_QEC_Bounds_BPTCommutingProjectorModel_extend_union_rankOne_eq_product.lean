-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extend_union_rankOne_eq_product
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extend_union_rankOne_eq_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:34.077517+00:00
-- url     : https://prove2.me/theorems/c99708be-1395-4ff7-b184-7c60cbeecebc
-- title:
--   BPTCommuting Projector Model: extend union rank One eq product
-- statement:
--   The preceding coordinate identity reflects back to the physical register as a
--   product of one local matrix unit on each separated region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L439-L526
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean#L439-L526

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.extend_union_rankOne_eq_product
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right)
    (labels labels' : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    let A := M.regionSubsystem left
    let B := M.regionSubsystem right
    let R := M.regionSubsystem (left ∪ right)
    let hAB : Disjoint A.selected B.selected := by
      simpa [A, B] using hdisjoint
    let leftLabels := (M.splitUnionSelectedLabel left right labels).1
    let rightLabels := (M.splitUnionSelectedLabel left right labels).2
    let leftLabels' := (M.splitUnionSelectedLabel left right labels').1
    let rightLabels' := (M.splitUnionSelectedLabel left right labels').2
    R.extendLocalToRegister
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions) Complex labels)
        (EuclideanSpace.basisFun (Semantics.Qudit.Label R.selectedDimensions)
          Complex labels')).toLinearMap =
      A.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label A.selectedDimensions)
            Complex leftLabels')).toLinearMap *
      B.extendLocalToRegister
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
            Complex rightLabels)
          (EuclideanSpace.basisFun (Semantics.Qudit.Label B.selectedDimensions)
            Complex rightLabels')).toLinearMap := by sorry
