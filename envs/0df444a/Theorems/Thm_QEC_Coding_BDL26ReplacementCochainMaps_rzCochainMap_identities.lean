-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzCochainMap_identities
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzCochainMap_identities
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T01:07:22.604738+00:00
-- url     : https://prove2.me/theorems/723619d4-e8c8-428a-9515-4dac19b9f994
-- title:
--   BDL26 Replacement Cochain Maps: rz Cochain Map identities
-- statement:
--   The two explicit RZ cochain identities use the materialized successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L2004-L2010
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L2004-L2010

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzCochainMap_identities
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (S : OddScale) :
    (rzCoboundary0 P A4 S).comp (rzCochainMap P A4 S).map0 =
        (rzCochainMap P A4 S).map1.comp (tannerCoboundary0 P) ∧
      (rzCoboundary1 P A4 S).comp (rzCochainMap P A4 S).map1 =
        (rzCochainMap P A4 S).map2.comp (tannerCoboundary1 P) := by sorry
