-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzQZ_commutes
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzQZ_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:04:43.39264+00:00
-- url     : https://prove2.me/theorems/af14e979-2e2f-4620-8357-18544dcbbd27
-- title:
--   BDL26 RZLocal Replacement: rz QZ commutes
-- statement:
--   Adjacent Q-Z commutation for the actual cellular boundary of `rzCz`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16843-L16851
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16843-L16851

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzQZ_commutes (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (z : P.Z)
    (hqz : P.qz q z = true) (S : OddScale) :
    (rzQZDegreeOne P A q z hqz S).comp
        (qDoubleCylinderBoundary1 (transposePresentation P) q S) =
      (doubleCylinderBoundary1 (transposePresentation P) z S).comp
        (rzQZDegreeZero P A q z hqz S) := by sorry
