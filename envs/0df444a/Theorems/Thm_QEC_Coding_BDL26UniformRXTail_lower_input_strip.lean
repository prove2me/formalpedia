-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_input_strip
-- name    : QEC.Coding.BDL26UniformRXTail.lower_input_strip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:05:43.883192+00:00
-- url     : https://prove2.me/theorems/0266eee5-8449-405c-b191-4dc5e99369cc
-- title:
--   BDL26 Uniform RXTail: lower input strip
-- statement:
--   Boundary strips contribute no syndrome coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L73-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Input.lean#L73-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26DecodingGraph BDL26ReplacementSupport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26IndexedDecoder
open BDL26UniformHistoryObstruction BDL26OwnerParentObstruction
open BDL26RXLocalReplacement BDL26XLocalRadialParity
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformRXTail.lower_input_strip (S : OddScale) (n : Nat)
    (face : XStarFace (state S n).presentation (retainedX S n))
    (side : Fin 2) (i : Fin S.half) :
    lowerSyndromeRaw S n (.inl (.inl ⟨retainedX S n,
      .inr (subdivisionOriginalBoundaryEdge (state S n).presentation (retainedX S n) S
        (xStarFaceBoundaryEdge (state S n).presentation (retainedX S n) face side) i)⟩)) = 0 := by sorry
