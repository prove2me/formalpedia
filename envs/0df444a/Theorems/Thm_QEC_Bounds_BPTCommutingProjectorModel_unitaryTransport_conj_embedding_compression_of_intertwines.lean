-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_embedding_compression_of_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_embedding_compression_of_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:52.634117+00:00
-- url     : https://prove2.me/theorems/45b3be39-8fed-4448-a35b-b22681a24970
-- title:
--   BPTCommuting Projector Model: unitary Transport conj embedding compression of intertwines
-- statement:
--   An ambient unitary that intertwines a sector embedding conjugates a two-sided
--   sector compression exactly by the corresponding active unitary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L546-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L546-L577

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_embedding_compression_of_intertwines
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (E : Semantics.UnitaryTransport H H) (U : Semantics.UnitaryTransport S S)
    (hintertwines : E.toLinearEquiv.toLinearMap.comp J =
      J.comp U.toLinearEquiv.toLinearMap) (P : Semantics.Operator S) :
    E.conjOperator (J.comp (P.comp (LinearMap.adjoint J))) =
      J.comp ((U.conjOperator P).comp (LinearMap.adjoint J)) := by sorry
