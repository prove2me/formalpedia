-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_count
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:08.492476+00:00
-- url     : https://prove2.me/theorems/2105ff17-f36e-4747-bbd8-b6bd0edc326b
-- title:
--   Locality: dai Li Physical Greedy Subdivision count
-- statement:
--   The physical greedy group's count is the corrected exact Nat bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1030-L1045
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1030-L1045

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_count
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).length * d ≤
      20 * (daiLiAtomCounters P embedding threshold left right atoms).sum + d := by sorry
