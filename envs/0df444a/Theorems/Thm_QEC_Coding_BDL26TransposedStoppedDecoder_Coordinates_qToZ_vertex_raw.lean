-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_Coordinates_qToZ_vertex_raw
-- name    : QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.qToZ_vertex_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:22:15.394541+00:00
-- url     : https://prove2.me/theorems/fc8904d8-9cf5-4faf-970d-47d65da88999
-- title:
--   Coordinates: q To Z vertex raw
-- statement:
--   All raw center/neighbor/interior tags coincide. The chosen root edge
--   does not alter the fixed Q center; no path/owner record is identified.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L220-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Coordinates.lean#L220-L228

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Coordinates
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26TransposedStoppedDecoder QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement hiding Two
open BDL26RZLocalReplacement hiding Two
open BDL26RZMap1CoordinateBridge hiding Two
open BDL26RXDecoderAdapter
open MultiscaleDecoder (BDL26Field)
open scoped Classical BigOperators

theorem QEC.Coding.BDL26TransposedStoppedDecoder.Coordinates.qToZ_vertex_raw (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hz : P.qz q z = true) (S : OddScale)
    (root : QStarEdge (transposePresentation P) q)
    (v : QDoubleCylinderVertex (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hz S v =
      qToXDoubleCylinderVertexAtRoot (transposePresentation P) q z hz S root v := by sorry
