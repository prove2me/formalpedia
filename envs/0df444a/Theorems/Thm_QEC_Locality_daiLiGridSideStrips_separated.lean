-- Prove2me | Theorems.Thm_QEC_Locality_daiLiGridSideStrips_separated
-- name    : QEC.Locality.daiLiGridSideStrips_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:17.144488+00:00
-- url     : https://prove2.me/theorems/ad09879d-af51-406e-b67e-fb5e7c91fd3f
-- title:
--   Locality: dai Li Grid Side Strips separated
-- statement:
--   Distinct canonical grid-side strips are physically separated by at least
--   `ell`.  This is the finite replacement for the former periodic `AddCircle`
--   gap: same-orientation strips are separated by their vertex buffers, while a
--   vertical and a horizontal strip are separated in the horizontal coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1689-L1816
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1689-L1816

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.daiLiGridSideStrips_separated
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (hEll : 0 ≤ ell) (hWidth : 4 * ell ≤ w) (origin : ℝ × ℝ)
    (side other : DaiLiGridSideIndex) (hne : side ≠ other)
    {p q : ι}
    (hp : p ∈ daiLiGridSideStripQubits embedding w ell (2 * ell) origin side)
    (hq : q ∈ daiLiGridSideStripQubits embedding w ell (2 * ell) origin other) :
    ell ≤ embedding.distance p q := by sorry
