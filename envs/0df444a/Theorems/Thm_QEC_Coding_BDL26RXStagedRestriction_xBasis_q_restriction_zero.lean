-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_xBasis_q_restriction_zero
-- name    : QEC.Coding.BDL26RXStagedRestriction.xBasis_q_restriction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:55.724901+00:00
-- url     : https://prove2.me/theorems/87dfc0a2-84bb-48c9-877a-8af5b54eacf3
-- title:
--   BDL26 RXStaged Restriction: x Basis q restriction zero
-- statement:
--   A single X-owned basis error has zero restriction to every Q correction block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L56-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L56-L61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.xBasis_q_restriction_zero (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (b : DoubleCylinderEdge P x S) (q : P.Q) :
    (fun vertex : QDoubleCylinderVertex P q S =>
      canonicalBasisWord (F := BDL26Field) (Sum.inl ⟨x,b⟩ : RX1 P S) (Sum.inr ⟨q,vertex⟩)) = 0 := by sorry
