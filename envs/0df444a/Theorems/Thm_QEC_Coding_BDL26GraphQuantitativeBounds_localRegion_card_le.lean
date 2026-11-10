-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_localRegion_card_le
-- name    : QEC.Coding.BDL26GraphQuantitativeBounds.localRegion_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:00:40.936041+00:00
-- url     : https://prove2.me/theorems/bdb25ae7-1926-4f8c-bfcc-9ff3d11fcfac
-- title:
--   BDL26 Graph Quantitative Bounds: local Region card le
-- statement:
--   The actual finite local region obeys one bound at every level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L420-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GraphQuantitativeBounds.lean#L420-L437

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GraphQuantitativeBounds
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26RXLocalReplacement
open scoped BigOperators Classical

theorem QEC.Coding.BDL26GraphQuantitativeBounds.localRegion_card_le (S : OddScale) (n : Nat) (u : GraphVertex S n) :
    (localRegion S n u).card ≤ localCoordinateBound S := by sorry
