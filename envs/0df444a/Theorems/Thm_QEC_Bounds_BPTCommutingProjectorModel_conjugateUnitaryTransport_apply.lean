-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjugateUnitaryTransport_apply
-- name    : QEC.Bounds.BPTCommutingProjectorModel.conjugateUnitaryTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:42.993205+00:00
-- url     : https://prove2.me/theorems/5805091a-29ba-4051-a3b2-a893b3cf37ec
-- title:
--   BPTCommuting Projector Model: conjugate Unitary Transport apply
-- statement:
--   The coordinate conjugate applies the transport, local unitary, and inverse transport in order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L489-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L489-L495

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

theorem QEC.Bounds.BPTCommutingProjectorModel.conjugateUnitaryTransport_apply
    {A B : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] (T : Semantics.UnitaryTransport A B)
    (U : Semantics.UnitaryTransport B B) (x : A) :
    conjugateUnitaryTransport T U x = T.symm (U (T x)) := by sorry
