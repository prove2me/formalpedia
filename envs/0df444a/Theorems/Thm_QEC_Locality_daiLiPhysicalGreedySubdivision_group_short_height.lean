-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_short_height
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_group_short_height
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:51.545914+00:00
-- url     : https://prove2.me/theorems/6f002773-a787-44d9-9af2-a3be0aea52d8
-- title:
--   Locality: dai Li Physical Greedy Subdivision group short height
-- statement:
--   The short branch becomes the exact short-height alternative after collapsing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1281-L1296
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1281-L1296

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_group_short_height
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms)
    (hShort : piece.length ≤ 1) :
    (daiLiAtomGroupRectangle left right piece).2.2 -
      (daiLiAtomGroupRectangle left right piece).1.2 ≤ 10 * ell := by sorry
