-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_min_height
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_group_min_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:46.538309+00:00
-- url     : https://prove2.me/theorems/693d90cc-8628-4518-974d-002c29ad2af2
-- title:
--   Locality: dai Li Physical Greedy Subdivision group min height
-- statement:
--   The collapsed rectangle of every physical greedy group has the required minimum height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1262-L1278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1262-L1278

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_group_min_height
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    5 * ell ≤ (daiLiAtomGroupRectangle left right piece).2.2 -
      (daiLiAtomGroupRectangle left right piece).1.2 := by sorry
