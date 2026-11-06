-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_right
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_tensorMap_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:50:56.759209+00:00
-- url     : https://prove2.me/theorems/d898fa0e-1d0c-4c6e-8209-41169bb8db95
-- title:
--   BPTCommuting Projector Model: unitary RTensor conj tensor Map right
-- statement:
--   Right tensoring transports a right operator while preserving a left identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L815-L831
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L815-L831

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_tensorMap_right
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (J : Type u)
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator J) :
    (unitaryRTensor U J).conjOperator
        (TensorProduct.map (1 : Semantics.Operator H) A) =
      TensorProduct.map (1 : Semantics.Operator K) A := by sorry
