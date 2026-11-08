-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzQZDegreeOne_totalParity
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzQZDegreeOne_totalParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:00:20.917755+00:00
-- url     : https://prove2.me/theorems/d45c43bc-09aa-4c8d-b80a-0b4a147b05d7
-- title:
--   BDL26 RZLocal Replacement: rz QZDegree One total Parity
-- statement:
--   F09 Q-Z coordinate formula: total parity is unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16854-L16860
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16854-L16860

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzQZDegreeOne_totalParity (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale)
    (word : Word Field (QDoubleCylinderVertex (transposePresentation P) q S)) :
    totalParity (rzQZDegreeOne P A q z hqz S word) = totalParity word := by sorry
