-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZCohomology_oddEquiv_symm_mk
-- name    : QEC.Coding.BDL26RZCohomology.oddEquiv_symm_mk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:48:27.107457+00:00
-- url     : https://prove2.me/theorems/803ba4b0-f57f-4adc-8f31-b7f72621e59d
-- title:
--   BDL26 RZCohomology: odd Equiv symm mk
-- statement:
--   Backward representative formula on the actual upper recursive state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L162-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean#L162-L166

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u

theorem QEC.Coding.BDL26RZCohomology.oddEquiv_symm_mk (S : OddScale) (k : Nat)
    (w : Cocycle (state S (2 * k + 2)).presentation) :
    (oddEquiv S k).symm (classOf (state S (2 * k + 2)).presentation w) =
      classOf (state S (2 * k + 1)).presentation (oddBackwardCocycle S k w) := by sorry
