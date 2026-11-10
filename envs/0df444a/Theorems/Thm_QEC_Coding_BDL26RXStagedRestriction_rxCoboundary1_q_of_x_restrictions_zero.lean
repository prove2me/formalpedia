-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_rxCoboundary1_q_of_x_restrictions_zero
-- name    : QEC.Coding.BDL26RXStagedRestriction.rxCoboundary1_q_of_x_restrictions_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:20:29.579361+00:00
-- url     : https://prove2.me/theorems/94027e84-21b3-488a-9be1-4959cd6a9e24
-- title:
--   BDL26 RXStaged Restriction: rx Coboundary1 q of x restrictions zero
-- statement:
--   Owner-fibre zero is the actual-error premise, not merely zero X syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L43-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L43-L53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.rxCoboundary1_q_of_x_restrictions_zero
    (P : TannerSquarePresentation) (S : OddScale) (e : Word BDL26Field (RX1 P S))
    (hX : ∀ x, restrictWordLinear (fiberRegion (rxCorrectionOwner P S) (.x x)) e = 0)
    (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxCoboundary1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S)
        (fun vertex => e (Sum.inr ⟨q,vertex⟩)) a := by sorry
