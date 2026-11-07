-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_strict_rectangleBounds
-- name    : QEC.Locality.mem_daiLiKGeDRegionCore_strict_rectangleBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:05.482577+00:00
-- url     : https://prove2.me/theorems/cad19653-fd01-46d6-9941-2420268b6ab8
-- title:
--   Locality: mem dai Li KGe DRegion Core strict rectangle Bounds
-- statement:
--   Each selected core point is strictly inside all four sides of its own
--   physical source rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2415-L2432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2415-L2432

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

theorem QEC.Locality.mem_daiLiKGeDRegionCore_strict_rectangleBounds
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) (p : ι)
    (hp : p ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region) :
    (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1.1 + ell <
        (embedding.point p).1 ∧
      (embedding.point p).1 <
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2.1 - ell ∧
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1.2 + ell <
          (embedding.point p).2 ∧
          (embedding.point p).2 <
            (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2.2 - ell := by sorry
