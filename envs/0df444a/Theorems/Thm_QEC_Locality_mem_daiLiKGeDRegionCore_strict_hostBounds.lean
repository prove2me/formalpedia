-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_strict_hostBounds
-- name    : QEC.Locality.mem_daiLiKGeDRegionCore_strict_hostBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:00.482658+00:00
-- url     : https://prove2.me/theorems/60e30362-540e-4da4-8898-e6935a90fc84
-- title:
--   Locality: mem dai Li KGe DRegion Core strict host Bounds
-- statement:
--   Membership in a finite `k >= d` core gives strict `ell` bounds in the
--   host grid cell.  For a bad region those bounds pass through the concrete
--   #496 rectangle-to-parent endpoint theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2437-L2496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2437-L2496

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

theorem QEC.Locality.mem_daiLiKGeDRegionCore_strict_hostBounds
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEll : 0 < ell) (region : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (p : ι)
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region) :
    (gridOrigin w t).1 + (daiLiKGeDRegionHostCell region).1 * w + ell <
        (embedding.point p).1 ∧
      (embedding.point p).1 < (gridOrigin w t).1 +
        ((daiLiKGeDRegionHostCell region).1 + 1) * w - ell ∧
        (gridOrigin w t).2 + (daiLiKGeDRegionHostCell region).2 * w + ell <
          (embedding.point p).2 ∧
          (embedding.point p).2 < (gridOrigin w t).2 +
            ((daiLiKGeDRegionHostCell region).2 + 1) * w - ell := by sorry
