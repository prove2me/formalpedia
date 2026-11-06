-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conjOperator_eq_of_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conjOperator_eq_of_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:09:21.991613+00:00
-- url     : https://prove2.me/theorems/e8696deb-7d81-43b0-b677-4bc95631a5e7
-- title:
--   BPTCommuting Projector Model: unitary Transport conj Operator eq of intertwines
-- statement:
--   An intertwining equation identifies the corresponding conjugated operator.
--   This small algebraic step is used immediately to turn the unitary isotypic
--   coordinates into an equality of the actual overlap coefficient operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4007-L4024
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4007-L4024

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conjOperator_eq_of_intertwines
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (A : Semantics.Operator H)
    (B : Semantics.Operator K)
    (hintertwines : U.toLinearEquiv.toLinearMap.comp A =
      B.comp U.toLinearEquiv.toLinearMap) :
    U.conjOperator A = B := by sorry
