-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_right_comp_overlapLeftEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorMap_right_comp_overlapLeftEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:06:44.387207+00:00
-- url     : https://prove2.me/theorems/488bd5d2-8a27-4feb-af4f-df0ce3a0d07e
-- title:
--   BPTCommuting Projector Model: tensor Map right comp overlap Left Embedding
-- statement:
--   A right tensor action intertwines with the left overlap embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1544-L1553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1544-L1553

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorMap_right_comp_overlapLeftEmbedding
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a : A) (Z : Semantics.Operator B) :
    (TensorProduct.map (1 : Semantics.Operator A) Z).comp (overlapLeftEmbedding A B a) =
      (overlapLeftEmbedding A B a).comp Z := by sorry
