-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_connectingWeight_sum_le
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_connectingWeight_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:20:59.327967+00:00
-- url     : https://prove2.me/theorems/626471e7-0519-4332-820b-8c9d2a3401ea
-- title:
--   BDL26 RXLocal Replacement: x Local connecting Weight sum le
-- statement:
--   The actual connecting-map weight is subadditive under finite assembly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L502-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L502-L516

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_connectingWeight_sum_le
    {I : Type} [Fintype I] (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f : I → Word Field (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S (∑ i, f i) ≤ ∑ i, connectingWeight P A x S (f i) := by sorry
