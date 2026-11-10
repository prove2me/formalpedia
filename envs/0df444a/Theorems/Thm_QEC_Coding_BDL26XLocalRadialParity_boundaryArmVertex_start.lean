-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_boundaryArmVertex_start
-- name    : QEC.Coding.BDL26XLocalRadialParity.boundaryArmVertex_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:23.560283+00:00
-- url     : https://prove2.me/theorems/b094d141-71bf-400f-9e78-a8ed0c1e2153
-- title:
--   BDL26 XLocal Radial Parity: boundary Arm Vertex start
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the boundary Arm Vertex start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L131-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L131-L141

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.boundaryArmVertex_start
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (i : Fin S.half) :
    subdivisionBoundaryEdgeStart P x S (subdivisionOriginalBoundaryEdge P x S edge i) =
      boundaryArmVertex P x S edge i.castSucc := by sorry
