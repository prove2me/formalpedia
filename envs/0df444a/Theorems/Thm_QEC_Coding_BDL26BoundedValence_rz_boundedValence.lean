-- Prove2me | Theorems.Thm_QEC_Coding_BDL26BoundedValence_rz_boundedValence
-- name    : QEC.Coding.BDL26BoundedValence.rz_boundedValence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:20:43.816708+00:00
-- url     : https://prove2.me/theorems/07deb91c-c0b8-43bf-b5c2-94a6f1a778fc
-- title:
--   BDL26 Bounded Valence: rz bounded Valence
-- statement:
--   Actual RZ replacement preserves the fixed measured valence invariant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValenceSuccessors.lean#L206-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValenceSuccessors.lean#L206-L214

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26BoundedValence.rz_boundedValence (P : TannerSquarePresentation)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (S : OddScale) (h : BoundedValence P) :
    BoundedValence (BDL26RZLocalReplacement.rzReplacementPresentation
      P A4.toTannerSquareAdmissible S) := by sorry
