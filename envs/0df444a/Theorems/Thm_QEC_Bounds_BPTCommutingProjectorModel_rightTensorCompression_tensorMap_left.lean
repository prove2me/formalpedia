-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightTensorCompression_tensorMap_left
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_tensorMap_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:00:43.782981+00:00
-- url     : https://prove2.me/theorems/7d179e12-00aa-4f28-9f39-61e580848d46
-- title:
--   BPTCommuting Projector Model: right Tensor Compression tensor Map left
-- statement:
--   Compressing a literal `T tensor 1` block by a unit vector on the inert factor
--   recovers `T`.  The next reconstruction theorem uses this to define the left
--   projector in the BV03 block from the transported overlap projector itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1120-L1134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1120-L1134

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_tensorMap_left
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (T : Semantics.Operator A) (eta : B) (heta : ‖eta‖ = 1) :
    rightTensorCompression eta (TensorProduct.map T (1 : Semantics.Operator B)) = T := by sorry
