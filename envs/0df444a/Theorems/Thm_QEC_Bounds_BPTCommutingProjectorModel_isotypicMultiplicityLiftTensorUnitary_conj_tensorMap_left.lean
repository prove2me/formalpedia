-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:22.1329+00:00
-- url     : https://prove2.me/theorems/871123a2-db57-4ae6-b129-0382a1472e41
-- title:
--   BPTCommuting Projector Model: isotypic Multiplicity Lift Tensor Unitary conj tensor Map left
-- statement:
--   The lifted multiplicity coordinate change leaves a left tensor action intact
--   and carries its inert multiplicity identity to the lifted identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4109-L4133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4109-L4133

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityLiftTensorUnitary_conj_tensorMap_left
    (W : Type u) [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] (n : Nat) (A : Semantics.Operator W) :
    (isotypicMultiplicityLiftTensorUnitary W n).conjOperator
      (TensorProduct.map A
        (1 : Semantics.Operator (EuclideanSpace Complex (Fin n)))) =
      TensorProduct.map A
        (1 : Semantics.Operator (isotypicLiftedMultiplicity.{u} n)) := by sorry
