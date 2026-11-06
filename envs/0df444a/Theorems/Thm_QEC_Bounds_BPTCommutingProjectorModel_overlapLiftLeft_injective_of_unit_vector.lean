-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlapLiftLeft_injective_of_unit_vector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.overlapLiftLeft_injective_of_unit_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:39:13.937945+00:00
-- url     : https://prove2.me/theorems/6f835bd9-2df5-423d-81a8-e213fcb08578
-- title:
--   BPTCommuting Projector Model: overlap Lift Left injective of unit vector
-- statement:
--   Fixing a normalized exterior vector is a left inverse to the first overlap
--   lift.  The BPT first-cut use is to reflect self-adjointness of the transported
--   `MC` projector back to its local representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2115-L2132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2115-L2132

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

theorem QEC.Bounds.BPTCommutingProjectorModel.overlapLiftLeft_injective_of_unit_vector
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (eta : C) (heta : ‖eta‖ = 1) :
    Function.Injective (overlapLiftLeft (C := C) :
      Semantics.Operator (Semantics.CompositeSystem A B) →
        Semantics.Operator (Semantics.CompositeSystem
          (Semantics.CompositeSystem A B) C)) := by sorry
