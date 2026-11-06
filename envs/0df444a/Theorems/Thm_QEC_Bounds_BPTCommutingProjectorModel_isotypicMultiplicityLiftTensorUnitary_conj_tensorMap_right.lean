-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:20.997023+00:00
-- url     : https://prove2.me/theorems/8d6c5198-1e88-452e-a30b-6e587dc77f5d
-- title:
--   BPTCommuting Projector Model: isotypic Multiplicity Lift Tensor Unitary conj tensor Map right
-- statement:
--   The multiplicity lift carries `1 tensor R` to `1 tensor` its lifted matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4143-L4160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4143-L4160

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_right
    (W : Type u) [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] (n : Nat)
    (R : Semantics.Operator (EuclideanSpace Complex (Fin n))) :
    (isotypicMultiplicityLiftTensorUnitary W n).conjOperator
      (TensorProduct.map (1 : Semantics.Operator W) R) =
      TensorProduct.map (1 : Semantics.Operator W)
        (isotypicMultiplicityLiftConjOperator.{u} n R) := by sorry
