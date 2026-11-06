-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_count
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:07:08.482186+00:00
-- url     : https://prove2.me/theorems/85c7ad5e-21e8-440b-bf4e-ee944632d720
-- title:
--   Locality: dai Li Physical Greedy Rectangles count
-- statement:
--   The collapsed rectangle count retains the corrected single-rectangle bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1585-L1592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1585-L1592

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_count
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).length * d ≤
      20 * (daiLiAtomCounters P embedding threshold left right atoms).sum + d := by sorry
