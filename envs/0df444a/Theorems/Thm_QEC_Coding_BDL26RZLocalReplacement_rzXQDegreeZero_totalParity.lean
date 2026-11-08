-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzXQDegreeZero_totalParity
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzXQDegreeZero_totalParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:53:49.463297+00:00
-- url     : https://prove2.me/theorems/8408ce45-b767-4e56-aa4a-b9d73c1c292a
-- title:
--   BDL26 RZLocal Replacement: rz XQDegree Zero total Parity
-- statement:
--   F09 X-Q coordinate formula: the two copy coordinates map by the
--   codiagonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16232-L16239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16232-L16239

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzXQDegreeZero_totalParity (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (word : Word Field Two) :
    totalParity (rzXQDegreeZero P q x hxq S word) =
      word 0 + word 1 := by sorry
