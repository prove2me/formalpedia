-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_norm_isotypicLiftedMultiplicityUnitVector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.norm_isotypicLiftedMultiplicityUnitVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:01:19.338956+00:00
-- url     : https://prove2.me/theorems/740eb46c-2e8a-4c5a-a7cb-a7221364f21e
-- title:
--   BPTCommuting Projector Model: norm isotypic Lifted Multiplicity Unit Vector
-- statement:
--   The chosen lifted multiplicity coordinate is normalized.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4169-L4171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4169-L4171

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

theorem QEC.Bounds.BPTCommutingProjectorModel.norm_isotypicLiftedMultiplicityUnitVector (n : Nat) [NeZero n] :
    ‖isotypicLiftedMultiplicityUnitVector.{u} n‖ = 1 := by sorry
