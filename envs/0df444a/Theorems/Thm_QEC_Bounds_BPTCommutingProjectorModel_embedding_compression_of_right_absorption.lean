-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_embedding_compression_of_right_absorption
-- name    : QEC.Bounds.BPTCommutingProjectorModel.embedding_compression_of_right_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:45.145814+00:00
-- url     : https://prove2.me/theorems/26f6f666-c494-4d3b-8bca-05419a0625bc
-- title:
--   BPTCommuting Projector Model: embedding compression of right absorption
-- statement:
--   Right absorption by a sector embedding, together with commutation,
--   reconstructs an operator from its two-sided active-sector compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L513-L540
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L513-L540

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

theorem QEC.Bounds.BPTCommutingProjectorModel.embedding_compression_of_right_absorption
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (R : Semantics.Operator H)
    (hcommute : Commute R (J.comp (LinearMap.adjoint J)))
    (hactive : R * (J.comp (LinearMap.adjoint J)) = R) :
    R = J.comp (((LinearMap.adjoint J).comp
      (R.comp J)).comp (LinearMap.adjoint J)) := by sorry
