-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalConnectingWeight_fiber_neighbor_injective
-- name    : QEC.Coding.BDL26XLocalConnectingWeight.fiber_neighbor_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:25:18.714685+00:00
-- url     : https://prove2.me/theorems/1118cb6d-a92c-45ab-ab27-21513c9daa79
-- title:
--   BDL26 XLocal Connecting Weight: fiber neighbor injective
-- statement:
--   The BDL26 XLocal Connecting Weight construction uses the fiber neighbor injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L161-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalConnectingWeight.lean#L161-L171

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalConnectingWeight
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalConnectingWeight.fiber_neighbor_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : DoubleCylinderEdge P x S) :
    Function.Injective (fun d : Fiber P A x S e => d.val.1) := by sorry
