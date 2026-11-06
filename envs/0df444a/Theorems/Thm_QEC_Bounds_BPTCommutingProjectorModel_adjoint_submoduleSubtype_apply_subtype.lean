-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_submoduleSubtype_apply_subtype
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_submoduleSubtype_apply_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:00:28.807199+00:00
-- url     : https://prove2.me/theorems/49aadbce-fb0d-4d78-9251-bc6823b9a856
-- title:
--   BPTCommuting Projector Model: adjoint submodule Subtype apply subtype
-- statement:
--   The adjoint of a finite-dimensional subspace inclusion is its inverse on that subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3221-L3228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3221-L3228

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_submoduleSubtype_apply_subtype
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (p : Submodule Complex H) (vector : p) :
    LinearMap.adjoint p.subtype (p.subtype vector) = vector := by sorry
