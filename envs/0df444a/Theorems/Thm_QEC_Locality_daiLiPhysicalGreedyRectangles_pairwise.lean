-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedyRectangles_pairwise
-- name    : QEC.Locality.daiLiPhysicalGreedyRectangles_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:59:06.413369+00:00
-- url     : https://prove2.me/theorems/680dd10d-d8dc-48c9-b2dd-a2e09bc6ff81
-- title:
--   Locality: dai Li Physical Greedy Rectangles pairwise
-- statement:
--   The collapsed physical greedy rectangles have pairwise-disjoint half-open qubit assignments.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1494-L1530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1494-L1530

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

theorem QEC.Locality.daiLiPhysicalGreedyRectangles_pairwise
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) :
    DaiLiPairwiseDisjointQubitRectangles embedding
      (daiLiPhysicalGreedyRectangles P embedding threshold left right d atoms) := by sorry
