-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendAlongLinearIsometryUnitary_apply
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendAlongLinearIsometryUnitary_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:23:39.654147+00:00
-- url     : https://prove2.me/theorems/d8a3c677-4c22-48a9-bca3-9a0fea322675
-- title:
--   BPTCommuting Projector Model: extend Along Linear Isometry Unitary apply
-- statement:
--   The ambient lift agrees with the active unitary on the image of its isometric embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L454-L477
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L454-L477

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendAlongLinearIsometryUnitary_apply
    {A H : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : A →ₗᵢ[Complex] H)
    (U : Semantics.UnitaryTransport A A) (x : A) :
    extendAlongLinearIsometryUnitary J U (J x) = J (U x) := by sorry
