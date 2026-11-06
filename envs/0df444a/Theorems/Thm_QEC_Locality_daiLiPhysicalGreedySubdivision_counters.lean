-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_counters
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_counters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:58:04.571617+00:00
-- url     : https://prove2.me/theorems/e3a9fff9-b299-455f-aeb8-705e1d11609a
-- title:
--   Locality: dai Li Physical Greedy Subdivision counters
-- statement:
--   The retained physical groups map exactly to the established Nat groups.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L987-L997
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L987-L997

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_counters
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).map
        (daiLiAtomCounters P embedding threshold left right) =
      daiLiGreedyAtomicSubdivision d
        (daiLiAtomCounters P embedding threshold left right atoms) := by sorry
