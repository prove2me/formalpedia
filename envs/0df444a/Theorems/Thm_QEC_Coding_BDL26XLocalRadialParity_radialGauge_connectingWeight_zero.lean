-- Prove2me | Theorems.Thm_QEC_Coding_BDL26XLocalRadialParity_radialGauge_connectingWeight_zero
-- name    : QEC.Coding.BDL26XLocalRadialParity.radialGauge_connectingWeight_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:32:28.525824+00:00
-- url     : https://prove2.me/theorems/8d1b2ad8-84d0-4166-9394-a3e9310144bc
-- title:
--   BDL26 XLocal Radial Parity: radial Gauge connecting Weight zero
-- statement:
--   The BDL26 XLocal Radial Parity construction uses the radial Gauge connecting Weight zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L274-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalRadialParity.lean#L274-L284

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalRadialParity
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

theorem QEC.Coding.BDL26XLocalRadialParity.radialGauge_connectingWeight_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field) :
    connectingWeight P A x S (radialGauge P A x S selected alpha) = 0 := by sorry
