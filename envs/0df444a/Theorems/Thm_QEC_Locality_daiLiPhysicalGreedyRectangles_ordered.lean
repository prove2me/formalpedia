-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_ordered
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:00:47.367291+00:00
-- url     : https://prove2.me/theorems/20fa4c3d-9243-48f3-ad10-309357e19e25
-- title:
--   Locality: dai Li Physical Greedy Rectangles ordered
-- statement:
--   The collapsed rectangles remain ordered by their common horizontal endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1533-L1560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1533-L1560

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_ordered
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms).IsChain
      (fun first second => first.2.2 = second.1.2) := by sorry
