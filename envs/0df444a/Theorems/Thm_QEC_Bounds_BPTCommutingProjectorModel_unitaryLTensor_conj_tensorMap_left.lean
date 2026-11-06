-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap_left
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryLTensor_conj_tensorMap_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:50:29.775977+00:00
-- url     : https://prove2.me/theorems/e6545c3e-b5e3-4552-9572-fa64f1f4e30d
-- title:
--   BPTCommuting Projector Model: unitary LTensor conj tensor Map left
-- statement:
--   Left tensoring transports a right operator while preserving a left identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L856-L872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L856-L872

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryLTensor_conj_tensorMap_left
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (I : Type u) [NormedAddCommGroup I] [InnerProductSpace Complex I]
    [Semantics.FiniteQuantumSystem I] (U : Semantics.UnitaryTransport H K)
    (A : Semantics.Operator H) :
    (unitaryLTensor I U).conjOperator
        (TensorProduct.map (1 : Semantics.Operator I) A) =
      TensorProduct.map (1 : Semantics.Operator I) (U.conjOperator A) := by sorry
