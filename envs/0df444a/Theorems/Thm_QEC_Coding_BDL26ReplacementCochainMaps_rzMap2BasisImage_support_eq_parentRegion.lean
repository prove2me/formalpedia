-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rzMap2BasisImage_support_eq_parentRegion
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rzMap2BasisImage_support_eq_parentRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:07:08.781232+00:00
-- url     : https://prove2.me/theorems/e34e6359-856a-4cc4-a78c-32508162edcb
-- title:
--   BDL26 Replacement Cochain Maps: rz Map2 Basis Image support eq parent Region
-- statement:
--   The BDL26 Replacement Cochain Maps construction uses the rz Map2 Basis Image support eq parent Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1907-L1915
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L1907-L1915

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rzMap2BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (z : P.Z) :
    hammingSupport (rzMap2BasisImage P A4 S z) =
      rzMap2ParentRegion P A4 S z := by sorry
