-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementCochainMaps_rxMap2BasisImage_support_eq_parentRegion
-- name    : QEC.Coding.BDL26ReplacementCochainMaps.rxMap2BasisImage_support_eq_parentRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:04:21.572972+00:00
-- url     : https://prove2.me/theorems/ed1ee1a8-0e80-410f-ad68-3f1d97e0af69
-- title:
--   BDL26 Replacement Cochain Maps: rx Map2 Basis Image support eq parent Region
-- statement:
--   The BDL26 Replacement Cochain Maps construction uses the rx Map2 Basis Image support eq parent Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L221-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementCochainMaps.lean#L221-L227

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

theorem QEC.Coding.BDL26ReplacementCochainMaps.rxMap2BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (S : OddScale) (z : P.Z) :
    hammingSupport (rxMap2BasisImage P S z) = rxMap2ParentRegion P S z := by sorry
