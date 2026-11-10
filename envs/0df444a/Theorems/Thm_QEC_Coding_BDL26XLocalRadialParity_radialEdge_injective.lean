-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialEdge_injective
-- name    : QEC.Coding.BDL26XLocalRadialParity.radialEdge_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:30.688538+00:00
-- url     : https://prove2.me/theorems/f6bab513-b755-407e-a8c8-7d92562b9368
-- title:
--   BDL26 XLocal Radial Parity: radial Edge injective
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the radial Edge injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L257-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L257-L264

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.radialEdge_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    Function.Injective (radialEdge P A x) := by sorry
