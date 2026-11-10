-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocal_terminal_weight_le_of_centers_zero
-- name    : QEC.Coding.BDL26RXLocalReplacement.qLocal_terminal_weight_le_of_centers_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:09.845191+00:00
-- url     : https://prove2.me/theorems/8052df90-ffa7-4dd3-803e-28c32e6ebd97
-- title:
--   BDL26 RXLocal Replacement: q Local terminal weight le of centers zero
-- statement:
--   With both cone points zero, each terminal bit is paid for by its own arm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L162-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L162-L178

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.qLocal_terminal_weight_le_of_centers_zero
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S))
    (hzero : f (0, Sum.inl (Sum.inl ())) = 0)
    (hone : f (1, Sum.inl (Sum.inl ())) = 0) :
    (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) ≤
      HammingWeight (wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) f) := by sorry
