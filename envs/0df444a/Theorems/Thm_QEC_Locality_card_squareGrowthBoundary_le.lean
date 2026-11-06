-- Prove2me | Theorems.Thm_QEC_Locality_card_squareGrowthBoundary_le
-- name    : QEC.Locality.card_squareGrowthBoundary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:10.466453+00:00
-- url     : https://prove2.me/theorems/543b233e-0177-4438-84dc-45e2c3f0ed42
-- title:
--   Locality: card square Growth Boundary le
-- statement:
--   One growth boundary is bounded by the exact geometric shell estimate plus the
--   actual long-interaction incidence counter over the inner square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L294-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L294-L319

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.card_squareGrowthBoundary_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (center : ℝ × ℝ)
    (outerRadius threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (hdiameter : 1 ≤ 2 * outerRadius) :
    ((squareGrowthBoundary P embedding center outerRadius threshold).selected.card : ℝ) ≤
      48 * outerRadius * threshold +
        ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) := by sorry
