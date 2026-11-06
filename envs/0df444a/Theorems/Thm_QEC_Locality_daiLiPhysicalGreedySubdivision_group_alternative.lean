-- Prove2me | Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_alternative
-- name    : QEC.Locality.daiLiPhysicalGreedySubdivision_group_alternative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:59.168324+00:00
-- url     : https://prove2.me/theorems/5498f508-6f9d-4064-8147-4a47053683af
-- title:
--   Locality: dai Li Physical Greedy Subdivision group alternative
-- statement:
--   Every collapsed physical group has the corrected low-counter or short-height alternative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1325-L1349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1325-L1349

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

theorem QEC.Locality.daiLiPhysicalGreedySubdivision_group_alternative
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    10 * regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle
          (daiLiAtomGroupRectangle left right piece).1
          (daiLiAtomGroupRectangle left right piece).2) ≤ d ∨
      (daiLiAtomGroupRectangle left right piece).2.2 -
        (daiLiAtomGroupRectangle left right piece).1.2 ≤ 10 * ell := by sorry
