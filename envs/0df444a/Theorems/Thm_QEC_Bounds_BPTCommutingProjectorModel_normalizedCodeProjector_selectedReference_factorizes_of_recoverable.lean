-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_normalizedCodeProjector_selectedReference_factorizes_of_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjector_selectedReference_factorizes_of_recoverable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:39.512933+00:00
-- url     : https://prove2.me/theorems/d4973ba3-09e2-42a9-8541-e3d1ac8904ed
-- title:
--   BPTCommuting Projector Model: normalized Code Projector selected Reference factorizes of recoverable
-- statement:
--   For the normalized whole-code state, concrete recovery from a BPT region
--   decouples that region from an arbitrary purifying reference.  This is the
--   recovery-to-reference input for the source no-cloning step: applying it to
--   both residual complementary factors forces the logical reference to be pure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L143-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L143-L161

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

theorem QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjector_selectedReference_factorizes_of_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hcorrectable : M.RegionErasureRecoverable region)
    (Ref : Type) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [Semantics.FiniteQuantumSystem Ref]
    (purification : Semantics.DensityOperator.FinitePurification
      (M.normalizedCodeProjectorDensity hcode) Ref) :
    (M.regionSubsystem region).selectedReferenceMarginal Ref
      (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one) =
      Semantics.DensityOperator.tensorDensity
        ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity
          (M.normalizedCodeProjectorDensity hcode))
        (Semantics.DensityOperator.leftMarginal
          (Semantics.DensityOperator.pureDensity purification.vector purification.normSq_one)) := by sorry
