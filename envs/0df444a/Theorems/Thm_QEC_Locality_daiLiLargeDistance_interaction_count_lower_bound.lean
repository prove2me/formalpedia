-- Prove2me | Theorems.Thm_QEC_Locality_daiLiLargeDistance_interaction_count_lower_bound
-- name    : QEC.Locality.daiLiLargeDistance_interaction_count_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:22.341586+00:00
-- url     : https://prove2.me/theorems/3dd03521-b21b-4ef6-9306-ed561803eb29
-- title:
--   Locality: dai Li Large Distance interaction count lower bound
-- statement:
--   Contrapositive count conclusion of DL24 Part I.  In the exact finite
--   large-distance branch, the actual `Finset (Sym2 ι)` of unordered
--   fixed-generator interactions has at least `d / 200` elements at Euclidean
--   length at least `d / (200 sqrt n)`, in coefficient form to avoid rounding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L2645-L2660
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L2645-L2660

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLiLargeDistance_interaction_count_lower_bound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hAboveBPT : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2)
    (hLargeDistance : Real.sqrt ((P.encodedQubits : ℝ) * (Fintype.card ι : ℝ)) ≤ d)
    (hEncodedPositive : 0 < P.encodedQubits) :
    d ≤ 200 * P.longInteractionCount embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι)) := by sorry
