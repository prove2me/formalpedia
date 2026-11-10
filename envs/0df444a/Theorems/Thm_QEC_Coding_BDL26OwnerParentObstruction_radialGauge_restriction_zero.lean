-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_radialGauge_restriction_zero
-- name    : QEC.Coding.BDL26OwnerParentObstruction.radialGauge_restriction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:17:28.258867+00:00
-- url     : https://prove2.me/theorems/337f9783-68b1-4d66-bd97-935e707c07f1
-- title:
--   BDL26 Owner Parent Obstruction: radial Gauge restriction zero
-- statement:
--   Zero connecting cost means every actual adjacent Q restriction vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L172-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerParentObstruction.lean#L172-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerParentObstruction
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps MultiscaleDecoder
open scoped Classical
open BDL26XLocalRadialParity BDL26XLocalConnectingWeight
open scoped BigOperators

theorem QEC.Coding.BDL26OwnerParentObstruction.radialGauge_restriction_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (x : P.X)
    (selected : Fin 2) (alpha : Neighbor P x → BDL26Field)
    (q : P.Q) (hq : P.xq x q = true) :
    rxXQDegreeOne P A q x hq S (radialGauge P A x S selected alpha) = 0 := by sorry
