-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToXDoubleCylinderEdge_end
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qToXDoubleCylinderEdge_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:37:31.384643+00:00
-- url     : https://prove2.me/theorems/119968ab-24b1-4fb0-9794-80c382df992e
-- title:
--   BDL26 Tanner Local Regularity: q To XDouble Cylinder Edge end
-- statement:
--   The Q-to-X cylinder cell embedding commutes with end endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3044-L3057
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3044-L3057

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qToXDoubleCylinderEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true)
    (S : OddScale) (edge : QDoubleCylinderEdge P q S) :
    qToXDoubleCylinderVertex P A q x hxq S
        (qDoubleCylinderEdgeEnd P q S edge) =
      tannerDoubleCylinderEdgeEnd P x S
        (qToXDoubleCylinderEdge P A q x hxq S edge) := by sorry
