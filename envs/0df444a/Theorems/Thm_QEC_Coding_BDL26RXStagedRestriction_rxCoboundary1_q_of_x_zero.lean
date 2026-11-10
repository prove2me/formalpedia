-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_rxCoboundary1_q_of_x_zero
-- name    : QEC.Coding.BDL26RXStagedRestriction.rxCoboundary1_q_of_x_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:33.303107+00:00
-- url     : https://prove2.me/theorems/f53b9fa4-88b6-4c7f-8c65-d54846d525ce
-- title:
--   BDL26 RXStaged Restriction: rx Coboundary1 q of x zero
-- statement:
--   Actual materialized Q restriction after all X correction coordinates vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L29-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L29-L40

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.rxCoboundary1_q_of_x_zero (P : TannerSquarePresentation) (S : OddScale)
    (e : Word BDL26Field (RX1 P S))
    (hX : ∀ x edge, e (Sum.inl ⟨x,edge⟩) = 0)
    (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => e (Sum.inr ⟨q,vertex⟩)) a := by sorry
