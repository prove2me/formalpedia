-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_qzConnecting_at_q
-- name    : QEC.Coding.BDL26RXStagedRestriction.qzConnecting_at_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:19:54.151181+00:00
-- url     : https://prove2.me/theorems/7b1e53c5-698a-42a4-89cf-ccb510ab50f6
-- title:
--   BDL26 RXStaged Restriction: qz Connecting at q
-- statement:
--   The Q-to-Z connecting term has no Q syndrome coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L20-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean#L20-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXStagedRestriction.qzConnecting_at_q (P : TannerSquarePresentation) (S : OddScale)
    (e : Word BDL26Field (RX1 P S)) (q : P.Q) (a : QDoubleCylinderEdge P q S) :
    rxConnectingQZ1 P S e (Sum.inl (Sum.inr ⟨q,a⟩)) = 0 := by sorry
