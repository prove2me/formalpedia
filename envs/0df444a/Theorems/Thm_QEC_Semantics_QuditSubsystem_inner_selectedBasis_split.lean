-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_inner_selectedBasis_split
-- name    : QEC.Semantics.QuditSubsystem.inner_selectedBasis_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:34.104715+00:00
-- url     : https://prove2.me/theorems/b01aadca-8291-4abc-816c-d9060934762f
-- title:
--   Qudit Subsystem: inner selected Basis split
-- statement:
--   Inner products of `T` selected basis vectors split into `S` and `T \ S` components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L666-L683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L666-L683

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

theorem QEC.Semantics.QuditSubsystem.inner_selectedBasis_split (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (x y : Qudit.Label T.selectedDimensions) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex y)
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex x) =
      inner Complex
          (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (S.splitSelectedLabel T hST y).1)
          (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (S.splitSelectedLabel T hST x).1) *
        inner Complex
          (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
            (S.splitSelectedLabel T hST y).2)
          (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
            (S.splitSelectedLabel T hST x).2) := by sorry
