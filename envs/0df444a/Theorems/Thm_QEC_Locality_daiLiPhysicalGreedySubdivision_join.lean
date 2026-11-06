-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_join
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_join
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:45.843453+00:00
-- url     : https://prove2.me/theorems/3b4260ad-47b4-47d8-90c6-9a953328107c
-- title:
--   Locality: dai Li Physical Greedy Subdivision join
-- statement:
--   The physical greedy groups cover every input atom in original order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1000-L1007
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1000-L1007

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_join
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).flatten = atoms := by sorry
