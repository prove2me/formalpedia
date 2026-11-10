-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxCochainMap_identities
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rxCochainMap_identities
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:07:05.70168+00:00
-- url     : https://prove2.me/theorems/1099253c-2e90-4c7b-b897-dbfc9e92df29
-- title:
--   BDL26 Replacement Cochain Maps: rx Cochain Map identities
-- statement:
--   The two concrete RX cochain identities target the assembled raw RX complex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1995-L2001
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1995-L2001

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26ReplacementCochainMaps
open scoped BigOperators Classical
open QEC.Coding
open QEC.Coding.BDL26FiniteTannerSquare
open QEC.Coding.BDL26TannerLocalRegularity
open QEC.Coding.BDL26RXLocalReplacement
open QEC.Coding.BDL26RZLocalReplacement
open QEC.Coding.BDL26RZMap1CoordinateBridge
open QEC.Coding.MultiscaleDecoder

theorem QEC.Coding.BDL26ReplacementCochainMaps.rxCochainMap_identities
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale) :
    (rxCoboundary0 P S).comp (rxMap P S).map0 =
        (rxMap P S).map1.comp (tannerCoboundary0 P) ∧
      (rxCoboundary1 P S).comp (rxMap P S).map1 =
        (rxMap P S).map2.comp (tannerCoboundary1 P) := by sorry
