-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeSectorPhysicalUnitary_conj_embedding_compression
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeSectorPhysicalUnitary_conj_embedding_compression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:11:29.444919+00:00
-- url     : https://prove2.me/theorems/cb848fe5-de30-4286-93e2-17d66ca50733
-- title:
--   BPTCommuting Projector Model: active Sector Physical Unitary conj embedding compression
-- statement:
--   Conjugating a compressed active-sector operator by the physical lift is
--   exactly conjugation by its prescribed active coordinate unitary.  In
--   particular, arbitrary choices made by the ambient extension are invisible on
--   operators reconstructed through the sector embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L756-L778
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L756-L778

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

theorem QEC.Bounds.BPTCommutingProjectorModel.activeSectorPhysicalUnitary_conj_embedding_compression
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC))
    (P : Semantics.Operator (Semantics.CompositeSystem SB SC)) :
    (activeSectorPhysicalUnitary SB SC UB UC U).conjOperator
        ((submoduleTensorEmbedding SB SC).toLinearMap.comp
          (P.comp (LinearMap.adjoint (submoduleTensorEmbedding SB SC).toLinearMap))) =
      (submoduleTensorEmbedding SB SC).toLinearMap.comp
        (((conjugateUnitaryTransport
          (activeSectorCoordinateTransport SB SC UB UC)
          (unitaryLTensor WB (unitaryRTensor U NC))).conjOperator P).comp
          (LinearMap.adjoint (submoduleTensorEmbedding SB SC).toLinearMap)) := by sorry
