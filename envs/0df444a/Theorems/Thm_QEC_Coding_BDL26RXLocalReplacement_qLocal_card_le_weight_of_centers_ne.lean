-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocal_card_le_weight_of_centers_ne
-- name    : QEC.Coding.BDL26RXLocalReplacement.qLocal_card_le_weight_of_centers_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:46.421502+00:00
-- url     : https://prove2.me/theorems/852de45c-031b-4d8f-b6a9-3cf1fe26c0d8
-- title:
--   BDL26 RXLocal Replacement: q Local card le weight of centers ne
-- statement:
--   Different cone-point bits force one syndrome per disjoint leaf path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L181-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L181-L208

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.qLocal_card_le_weight_of_centers_ne
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S))
    (hne : f (0, Sum.inl (Sum.inl ())) ≠ f (1, Sum.inl (Sum.inl ()))) :
    Fintype.card (QStarEdge P q) ≤
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f) := by sorry
