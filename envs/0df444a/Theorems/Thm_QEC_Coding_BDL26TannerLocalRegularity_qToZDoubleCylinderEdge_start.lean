-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_qToZDoubleCylinderEdge_start
-- name    : QEC.Coding.BDL26TannerLocalRegularity.qToZDoubleCylinderEdge_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:33:32.575744+00:00
-- url     : https://prove2.me/theorems/f795b853-47e4-4b93-9c5d-dc85d1067b8f
-- title:
--   BDL26 Tanner Local Regularity: q To ZDouble Cylinder Edge start
-- statement:
--   The transpose-derived Q-to-Z embedding commutes with start endpoints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3060-L3073
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L3060-L3073

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

theorem QEC.Coding.BDL26TannerLocalRegularity.qToZDoubleCylinderEdge_start
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) (S : OddScale)
    (edge : QDoubleCylinderEdge (transposePresentation P) q S) :
    qToZDoubleCylinderVertex P A q z hqz S
        (qDoubleCylinderEdgeStart (transposePresentation P) q S edge) =
      tannerDoubleCylinderEdgeStart (transposePresentation P) z S
        (qToZDoubleCylinderEdge P A q z hqz S edge) := by sorry
