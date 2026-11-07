-- Prove2me | Theorems.Thm_QEC_Locality_daiLiStrictGridCellInteriors_separated
-- name    : QEC.Locality.daiLiStrictGridCellInteriors_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:02.571204+00:00
-- url     : https://prove2.me/theorems/87fbdf04-1833-4d28-bb1a-677cd6b6f0df
-- title:
--   Locality: dai Li Strict Grid Cell Interiors separated
-- statement:
--   Strict `ell` interiors of two distinct physical grid cells are separated
--   by at least `ell`.  This is stated directly on coordinates so both good cells
--   and bad-cell subdivision rectangles can share it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1636-L1683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1636-L1683

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

theorem QEC.Locality.daiLiStrictGridCellInteriors_separated
    (embedding : UnitSeparatedEmbedding2D ι) {w ell : ℝ}
    (hEll : 0 ≤ ell) (hWidth : 0 ≤ w) (origin : ℝ × ℝ)
    (cell other : ℤ × ℤ) (hne : cell ≠ other) {p q : ι}
    (hp : origin.1 + (cell.1 : ℝ) * w + ell < (embedding.point p).1 ∧
      (embedding.point p).1 < origin.1 + ((cell.1 : ℝ) + 1) * w - ell ∧
        origin.2 + (cell.2 : ℝ) * w + ell < (embedding.point p).2 ∧
          (embedding.point p).2 < origin.2 + ((cell.2 : ℝ) + 1) * w - ell)
    (hq : origin.1 + (other.1 : ℝ) * w + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < origin.1 + ((other.1 : ℝ) + 1) * w - ell ∧
        origin.2 + (other.2 : ℝ) * w + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < origin.2 + ((other.2 : ℝ) + 1) * w - ell) :
    ell ≤ embedding.distance p q := by sorry
