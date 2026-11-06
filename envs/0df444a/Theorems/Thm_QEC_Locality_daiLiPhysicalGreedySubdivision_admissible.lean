-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_admissible
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:44.955331+00:00
-- url     : https://prove2.me/theorems/d82d33e8-1e76-42ea-962a-44fd7e4456e1
-- title:
--   Locality: dai Li Physical Greedy Subdivision admissible
-- statement:
--   Every retained physical group is nonempty and low-counter or one short atom.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1010-L1027
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1010-L1027

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_admissible
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms piece : List (ℝ × ℝ))
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece ≠ [] ∧
      (10 * (daiLiAtomCounters P embedding threshold left right piece).sum ≤ d ∨
        piece.length ≤ 1) := by sorry
