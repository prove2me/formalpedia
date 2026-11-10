-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_boundaryArmVertex_end
-- name    : QEC.Coding.BDL26XLocalRadialParity.boundaryArmVertex_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:21.240511+00:00
-- url     : https://prove2.me/theorems/1879ae29-3a38-47ce-9d3a-7eebd4be7461
-- title:
--   BDL26 XLocal Radial Parity: boundary Arm Vertex end
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the boundary Arm Vertex end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L143-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L143-L152

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.boundaryArmVertex_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (i : Fin S.half) :
    subdivisionBoundaryEdgeEnd P x S (subdivisionOriginalBoundaryEdge P x S edge i) =
      boundaryArmVertex P x S edge i.succ := by sorry
