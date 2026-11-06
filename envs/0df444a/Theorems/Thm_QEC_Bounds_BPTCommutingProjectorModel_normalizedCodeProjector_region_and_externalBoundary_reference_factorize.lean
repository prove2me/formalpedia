-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_normalizedCodeProjector_region_and_externalBoundary_reference_factorize
-- name    : QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjector_region_and_externalBoundary_reference_factorize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:09:52.543746+00:00
-- url     : https://prove2.me/theorems/ac9ff8f6-6257-4f89-ac59-156316663c7d
-- title:
--   BPTCommuting Projector Model: normalized Code Projector region and external Boundary reference factorize
-- statement:
--   Both BPT recoverability hypotheses give independent reference-decoupling
--   factorizations for the same normalized full-code purification.  The first
--   factorization is for `M`; the second is for `partialPlus M`.  Their residual
--   counterparts are the two decouplings used by the source no-cloning argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L169-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L169-L195

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjector_region_and_externalBoundary_reference_factorize
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hregion : M.RegionErasureRecoverable region)
    (hexternal : M.RegionErasureRecoverable (M.externalBoundary region))
    (Ref : Type) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [Semantics.FiniteQuantumSystem Ref]
    (purification : Semantics.DensityOperator.FinitePurification
      (M.normalizedCodeProjectorDensity hcode) Ref) :
    ((M.regionSubsystem region).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one))) ∧
    ((M.regionSubsystem (M.externalBoundary region)).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem (M.externalBoundary region)).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one))) := by sorry
