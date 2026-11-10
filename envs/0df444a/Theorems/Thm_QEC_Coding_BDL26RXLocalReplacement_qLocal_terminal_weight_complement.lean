-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_qLocal_terminal_weight_complement
-- name    : QEC.Coding.BDL26RXLocalReplacement.qLocal_terminal_weight_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:30:14.277205+00:00
-- url     : https://prove2.me/theorems/5e7dc378-9446-4789-ad3f-f06c03b729ef
-- title:
--   BDL26 RXLocal Replacement: q Local terminal weight complement
-- statement:
--   Complementary terminal words have total weight twice the leaf count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L211-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/QLocalWeight.lean#L211-L230

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.qLocal_terminal_weight_complement
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale)
    (f : Word Field (QDoubleCylinderVertex P q S)) :
    (∑ z : QStarEdge P q, HammingWeight (rxQZDegreeOne P q z.val z.property S f)) +
        (∑ z : QStarEdge P q, HammingWeight
          (rxQZDegreeOne P q z.val z.property S (fun v => f v + 1))) =
      2 * Fintype.card (QStarEdge P q) := by sorry
