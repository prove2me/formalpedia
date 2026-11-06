-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_quditSubsystem_extendLocalToRegister_mul_complementOperator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.quditSubsystem_extendLocalToRegister_mul_complementOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:02.552949+00:00
-- url     : https://prove2.me/theorems/69c7d2de-3768-4269-87b0-9494d198046d
-- title:
--   BPTCommuting Projector Model: qudit Subsystem extend Local To Register mul complement Operator
-- statement:
--   Recombine a selected-factor operator with a literal complement-factor operator
--   on a concrete register.  The statement is kept local because D5 needs the
--   exact endpoint expression rather than a support-only reformulation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5249-L5262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L5249-L5262

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

theorem QEC.Bounds.BPTCommutingProjectorModel.quditSubsystem_extendLocalToRegister_mul_complementOperator
    (S : Semantics.QuditSubsystem L.localDimension)
    (A : Semantics.Operator S.selectedSystem) (P : Semantics.Operator S.complementSystem) :
    S.extendLocalToRegister A *
        (S.registerFactorization.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)) =
      S.registerFactorization.symm.conjOperator (TensorProduct.map A P) := by sorry
