-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDRegionCores_separated
-- name    : QEC.Locality.daiLiKGeDRegionCores_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:53.679319+00:00
-- url     : https://prove2.me/theorems/e7846937-2ddb-45f1-b3a5-22d45eeb4a25
-- title:
--   Locality: dai Li KGe DRegion Cores separated
-- statement:
--   Distinct finite `k >= d` source-region cores are geometrically separated.
--   Different host cells use strict grid interiors; two entries in one bad cell use
--   the proved order of the actual greedy rectangle list.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2501-L2617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2501-L2617

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

theorem QEC.Locality.daiLiKGeDRegionCores_separated
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
    (hEll : 0 < ell) (hWidth : 0 < w)
    (region other : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hOther : other ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles)
    (hne : region ≠ other) {p q : ι}
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles region)
    (hq : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles other) :
    ell ≤ embedding.distance p q := by sorry
