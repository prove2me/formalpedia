-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_normalizedCodeProjectorDensity_supportedOn
-- name    : QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjectorDensity_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:29.123727+00:00
-- url     : https://prove2.me/theorems/47f2b6a8-69db-40f6-be98-2f5a9c493f0f
-- title:
--   BPTCommuting Projector Model: normalized Code Projector Density supported On
-- statement:
--   The normalized code-projector density is supported on the actual BPT code.
--   This is the support premise consumed by recovery-to-reference decoupling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L129-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L129-L135

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

theorem QEC.Bounds.BPTCommutingProjectorModel.normalizedCodeProjectorDensity_supportedOn
    (M : BPTCommutingProjectorModel L kappa) (hcode : M.codeSpace.carrier ≠ ⊥) :
    Semantics.DensityOperator.SupportedOn M.codeSpace
      (M.normalizedCodeProjectorDensity hcode) := by sorry
