-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxXQDegreeZero_one
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxXQDegreeZero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:44:32.555551+00:00
-- url     : https://prove2.me/theorems/45c13b33-4867-43c4-9d53-9d71b0be587c
-- title:
--   BDL26 RXLocal Replacement: rx XQDegree Zero one
-- statement:
--   Restricting the constant X generator gives the constant Q generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24460-L24465
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L24460-L24465

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u

theorem QEC.Coding.BDL26RXLocalReplacement.rxXQDegreeZero_one (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (q : P.Q) (x : P.X)
    (hxq : P.xq x q = true) (S : OddScale) :
    rxXQDegreeZero P A q x hxq S (1 : Word Field (DoubleCylinderVertex P x S)) =
      (1 : Word Field (QDoubleCylinderVertex P q S)) := by sorry
