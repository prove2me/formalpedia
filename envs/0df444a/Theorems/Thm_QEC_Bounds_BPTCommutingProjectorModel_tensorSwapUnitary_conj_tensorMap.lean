-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorSwapUnitary_conj_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorSwapUnitary_conj_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:51:26.078891+00:00
-- url     : https://prove2.me/theorems/416a8c2f-7867-4196-8074-9b09ac8592a9
-- title:
--   BPTCommuting Projector Model: tensor Swap Unitary conj tensor Map
-- statement:
--   Swapping two factors exchanges the two tensor-product operator factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1002-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1002-L1015

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorSwapUnitary_conj_tensorMap
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (A : Semantics.Operator H) (B : Semantics.Operator K) :
    (tensorSwapUnitary H K).conjOperator (TensorProduct.map A B) =
      TensorProduct.map B A := by sorry
