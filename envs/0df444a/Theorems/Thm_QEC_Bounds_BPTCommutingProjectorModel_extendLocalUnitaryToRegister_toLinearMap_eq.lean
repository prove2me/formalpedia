-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalUnitaryToRegister_toLinearMap_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendLocalUnitaryToRegister_toLinearMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:01:03.717308+00:00
-- url     : https://prove2.me/theorems/a4e05710-8626-4ce0-861b-b090527957c0
-- title:
--   BPTCommuting Projector Model: extend Local Unitary To Register to Linear Map eq
-- statement:
--   The global lift has exactly the concrete local-extension operator as its linear map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L379-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L379-L385

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendLocalUnitaryToRegister_toLinearMap_eq
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    (extendLocalUnitaryToRegister q S U).toLinearEquiv.toLinearMap =
      S.extendLocalToRegister U.toLinearEquiv.toLinearMap := by sorry
