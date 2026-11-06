-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_quditCoordinateRelabel_apply_basis
-- name    : QEC.Bounds.BPTCommutingProjectorModel.quditCoordinateRelabel_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:02:54.43836+00:00
-- url     : https://prove2.me/theorems/88c7c520-6d84-47aa-9d41-ab4fe858d073
-- title:
--   BPTCommuting Projector Model: qudit Coordinate Relabel apply basis
-- statement:
--   The coordinate relabeling sends every computational basis vector to its relabeled one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5224-L5233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5224-L5233

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

theorem QEC.Bounds.BPTCommutingProjectorModel.quditCoordinateRelabel_apply_basis
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {q : I → Nat} {r : J → Nat} (e : I ≃ J)
    (hdim : ∀ i, q i = r (e i)) (labels : Semantics.Qudit.Label q) :
    quditCoordinateRelabel e hdim
        (EuclideanSpace.basisFun (Semantics.Qudit.Label q) Complex labels) =
      EuclideanSpace.basisFun (Semantics.Qudit.Label r) Complex
        (quditLabelRelabel e hdim labels) := by sorry
