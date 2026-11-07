-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDRegionCore_subset_rectangle
-- name    : QEC.Locality.daiLiKGeDRegionCore_subset_rectangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:36.864724+00:00
-- url     : https://prove2.me/theorems/871051bc-d90a-409e-a7d9-84a092b1d5be
-- title:
--   Locality: dai Li KGe DRegion Core subset rectangle
-- statement:
--   Each strict core is a genuine subset of the closed source region from
--   which its CPTP recovery will be inherited.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2401-L2411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2401-L2411

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

theorem QEC.Locality.daiLiKGeDRegionCore_subset_rectangle
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) :
    daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region ⊆
      embedding.qubitsInRectangle
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2 := by sorry
