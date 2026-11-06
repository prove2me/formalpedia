-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_infix
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_infix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:26.818201+00:00
-- url     : https://prove2.me/theorems/336af067-c2a8-4711-8fda-da874382cfdc
-- title:
--   Locality: dai Li Physical Greedy Subdivision infix
-- statement:
--   A physical greedy group is a contiguous infix of the original atom list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1061-L1069
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1061-L1069

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_infix
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms piece : List (ℝ × ℝ))
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece <:+: atoms := by sorry
