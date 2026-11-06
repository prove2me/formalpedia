-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_counter
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_group_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:55.657506+00:00
-- url     : https://prove2.me/theorems/74be3532-2b9d-45bc-b53a-6dd2a42e5c05
-- title:
--   Locality: dai Li Physical Greedy Subdivision group counter
-- statement:
--   The counter carried by a physical greedy group is exactly the actual counter
--   of its collapsed rectangle, not merely a sum supplied as a hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1302-L1322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1302-L1322

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_group_counter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    (daiLiAtomCounters P embedding threshold left right piece).sum =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle
          (daiLiAtomGroupRectangle left right piece).1
          (daiLiAtomGroupRectangle left right piece).2) := by sorry
