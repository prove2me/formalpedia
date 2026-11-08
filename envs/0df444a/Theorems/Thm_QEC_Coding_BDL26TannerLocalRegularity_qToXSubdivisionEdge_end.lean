-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToXSubdivisionEdge_end
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qToXSubdivisionEdge_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:07.83419+00:00
-- url     : https://prove2.me/theorems/1739abfa-4981-4508-b0e4-909c2202c49c
-- title:
--   BDL26 Tanner Local Regularity: q To XSubdivision Edge end
-- statement:
--   The BDL26 Tanner Local Regularity construction uses the q To XSubdivision Edge end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2640-L2657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L2640-L2657

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qToXSubdivisionEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QSubdivisionEdge P q S) :
    qToXSubdivisionVertex P A q x hxq S (qSubdivisionEdgeEnd P q S edge) =
      subdivisionEdgeEnd P x S
        (qToXSubdivisionBoundaryEdge P q x hxq S edge).1 := by sorry
