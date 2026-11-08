-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzReplacementCellularRegular
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzReplacementCellularRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:03:26.24807+00:00
-- url     : https://prove2.me/theorems/c31d1aff-fcff-4ee4-9fe2-6a443945ca07
-- title:
--   BDL26 RZLocal Replacement: rz Replacement Cellular Regular
-- statement:
--   Cellular regularity of the concrete RZ successor.
--
--   The local and Q-Z glue families are constructor-injective.  Only the old-X
--   copy family consumes cellular regularity of the input presentation.  The V3
--   admissibility and cellular-regularity hypotheses remain separate: neither is
--   derived from the other.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L1790-L1898
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L1790-L1898

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzReplacementCellularRegular
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (S : OddScale) :
    TannerSquareCellularRegular
      (rzReplacementPresentation P
        A3.toTannerSquareAdmissibleV2.toTannerSquareAdmissible S) := by sorry
