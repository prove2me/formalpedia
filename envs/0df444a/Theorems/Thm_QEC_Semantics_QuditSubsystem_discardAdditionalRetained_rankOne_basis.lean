-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_discardAdditionalRetained_rankOne_basis
-- name    : QEC.Semantics.QuditSubsystem.discardAdditionalRetained_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:50.77047+00:00
-- url     : https://prove2.me/theorems/7fe93899-23cd-4847-b87b-1e02baf7f996
-- title:
--   Qudit Subsystem: discard Additional Retained rank One basis
-- statement:
--   Discarding the additional retained factor contracts its computational matrix units.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L744-L768
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L744-L768

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.discardAdditionalRetained_rankOne_basis (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (x y : Qudit.Label S.complementDimensions) :
    S.discardAdditionalRetained T hST
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex x)
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex y)).toLinearMap =
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST y).1)
        (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
          (S.splitComplementLabel T hST x).1)) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (S.splitComplementLabel T hST x).2)
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (S.splitComplementLabel T hST y).2)).toLinearMap := by sorry
