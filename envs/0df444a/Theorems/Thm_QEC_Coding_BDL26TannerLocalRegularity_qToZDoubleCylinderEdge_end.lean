-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZDoubleCylinderEdge_end
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qToZDoubleCylinderEdge_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:34:24.495131+00:00
-- url     : https://prove2.me/theorems/decae3fb-7370-4afb-9827-b25b01bbc39d
-- title:
--   BDL26 Tanner Local Regularity: q To ZDouble Cylinder Edge end
-- statement:
--   The transpose-derived Q-to-Z embedding commutes with end endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3076-L3089
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3076-L3089

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qToZDoubleCylinderEdge_end
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S
        (qDoubleCylinderEdgeEnd (transposePresentation P) q S edge) =
      tannerDoubleCylinderEdgeEnd (transposePresentation P) z S
        (qToZDoubleCylinderEdge P A q z hqz S edge) := by sorry
