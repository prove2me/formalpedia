-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finrank_carrier_le_one_of_all_scalar_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finrank_carrier_le_one_of_all_scalar_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:10.311721+00:00
-- url     : https://prove2.me/theorems/fae1e4c5-c50b-4c69-aea1-059e03d74200
-- title:
--   BPTCommuting Projector Model: finrank carrier le one of all scalar compression
-- statement:
--   If every ambient operator has scalar compression to a finite-dimensional code,
--   then that code has dimension at most one.  Mathematically, a rank-one probe
--   onto either member of a hypothetical independent pair would make the other
--   member a scalar multiple of it.  This is the rank-one engine used for the
--   source's `Pi_AB'` conclusion and, after both residual erasures are transported,
--   for the `Theta_{B''C'}` no-cloning conclusion (source lines 643-657).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5113-L5173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5113-L5173

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

theorem QEC.Bounds.BPTCommutingProjectorModel.finrank_carrier_le_one_of_all_scalar_compression
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (C : Semantics.QuantumCode H)
    (hscalar : ∀ A : Semantics.Operator H, ∃ scalar : Complex,
      C.projector * A * C.projector = scalar • C.projector) :
    Module.finrank Complex C.carrier ≤ 1 := by sorry
