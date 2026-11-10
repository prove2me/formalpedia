-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_lift_graphBoundary
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_lift_graphBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:21:06.066191+00:00
-- url     : https://prove2.me/theorems/9e1660d4-6195-4b36-98dc-75b11c40cab7
-- title:
--   BDL26 RXLocal Replacement: x Local lift graph Boundary
-- statement:
--   Lifting a proved endpoint profile commutes with the concrete coboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L454-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L454-L468

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_lift_graphBoundary
    {V E C F : Type}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype C] [DecidableEq C] [Fintype F] [DecidableEq F]
    (D : Word Field C →ₗ[Field] Word Field F)
    (start finish : E → V) (cellMap : V → F) (edgeMap : E → C)
    (h : ∀ e b, D (Pi.single (edgeMap e) b) =
      Pi.single (cellMap (start e)) b + Pi.single (cellMap (finish e)) b) :
    D.comp (xLocalWordPush edgeMap) =
      (xLocalWordPush cellMap).comp (graphBoundary start finish) := by sorry
