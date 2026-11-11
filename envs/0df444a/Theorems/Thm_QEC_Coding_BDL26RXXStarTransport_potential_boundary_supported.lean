-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_supported
-- name    : QEC.Coding.BDL26RXXStarTransport.potential_boundary_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:09:26.189682+00:00
-- url     : https://prove2.me/theorems/181b7661-88ea-40ee-8775-1166356ee065
-- title:
--   BDL26 RXXStar Transport: potential boundary supported
-- statement:
--   The BDL26 RXXStar Transport construction uses the potential boundary supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L192-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean#L192-L194

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

theorem QEC.Coding.BDL26RXXStarTransport.potential_boundary_supported (x : XCoord S i) (a b : Upper S depth i) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ (potential S depth i h x a b)) ⊆
      star1 S depth i h x := by sorry
