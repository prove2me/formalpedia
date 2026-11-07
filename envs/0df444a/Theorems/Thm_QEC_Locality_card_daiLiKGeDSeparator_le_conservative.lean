-- Prove2me | Theorems.Thm_QEC_Locality_card_daiLiKGeDSeparator_le_conservative
-- name    : QEC.Locality.card_daiLiKGeDSeparator_le_conservative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:13:36.539994+00:00
-- url     : https://prove2.me/theorems/5dda3cbd-f797-4d1b-9be6-57d163568dee
-- title:
--   Locality: card dai Li KGe DSeparator le conservative
-- statement:
--   Combining the actual separator components with the constructed subdivision
--   gives a source-routed `C` estimate.  The only long-interaction input is the
--   actual global endpoint-incidence total; no interaction lower bound is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1326-L1365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1326-L1365

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

theorem QEC.Locality.card_daiLiKGeDSeparator_le_conservative
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (d k : Nat) (hEll : 1 ≤ ell) (hD : 0 < d)
    (hCount : (∑ cell ∈ cells, (rectangles cell).length) * d ≤
      30 * daiLiBadGridTotalF P embedding threshold d w (gridOrigin w t))
    (hOverlap : daiLiBadGridTotalF P embedding threshold d w (gridOrigin w t) ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q)
    (hGlobal : 50 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) ≤ k) :
    ((daiLiKGeDSeparator P embedding threshold w ell t cells rectangles).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (∑ q : ι, P.daiLiInteractionCounter embedding threshold q : Nat) +
          960 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by sorry
