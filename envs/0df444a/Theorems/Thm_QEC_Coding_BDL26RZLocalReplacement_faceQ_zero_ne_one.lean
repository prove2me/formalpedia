-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_faceQ_zero_ne_one
-- name    : QEC.Coding.BDL26RZLocalReplacement.faceQ_zero_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:03:51.886599+00:00
-- url     : https://prove2.me/theorems/26b9f9e7-9daf-4e50-bb96-be813092c14a
-- title:
--   BDL26 RZLocal Replacement: face Q zero ne one
-- statement:
--   The two ordered corners of an original Tanner face are distinct; this is
--   derived from the presentation's sole perfect-pairing theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L278-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L278-L291

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.faceQ_zero_ne_one (P : TannerSquarePresentation) (face : P.Face) :
    P.faceQ face 0 ≠ P.faceQ face 1 := by sorry
