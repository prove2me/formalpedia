-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZSubdivisionEdge_end
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qToZSubdivisionEdge_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:17.54961+00:00
-- url     : https://prove2.me/theorems/a6d74c6a-152c-409f-9f9d-99d7dbfa83de
-- title:
--   BDL26 Tanner Local Regularity: q To ZSubdivision Edge end
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the q To ZSubdivision Edge end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2679-L2697
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2679-L2697

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u

theorem QEC.Coding.BDL26TannerLocalRegularity.qToZSubdivisionEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QSubdivisionEdge (transposePresentation P) q S) :
    qToZSubdivisionVertex P A q z hqz S
        (qSubdivisionEdgeEnd (transposePresentation P) q S edge) =
      subdivisionEdgeEnd (transposePresentation P) z S
        (qToZSubdivisionBoundaryEdge P q z hqz S edge).1 := by sorry
