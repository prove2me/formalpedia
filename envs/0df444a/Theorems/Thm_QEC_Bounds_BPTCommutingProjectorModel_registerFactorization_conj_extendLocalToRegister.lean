-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_registerFactorization_conj_extendLocalToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.registerFactorization_conj_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:50:19.541958+00:00
-- url     : https://prove2.me/theorems/637d1c6f-0907-46f4-9d5a-e3877e496c17
-- title:
--   BPTCommuting Projector Model: register Factorization conj extend Local To Register
-- statement:
--   Factoring a register exposes the local extension as a tensor with the complement identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L781-L789
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L781-L789

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

theorem QEC.Bounds.BPTCommutingProjectorModel.registerFactorization_conj_extendLocalToRegister
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q) (P : Semantics.Operator S.selectedSystem) :
    S.registerFactorization.conjOperator (S.extendLocalToRegister P) =
      TensorProduct.map P (1 : Semantics.Operator S.complementSystem) := by sorry
