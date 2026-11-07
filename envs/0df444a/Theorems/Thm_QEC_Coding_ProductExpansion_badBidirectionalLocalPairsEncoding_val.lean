-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badBidirectionalLocalPairsEncoding_val
-- name    : QEC.Coding.ProductExpansion.badBidirectionalLocalPairsEncoding_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:24.514583+00:00
-- url     : https://prove2.me/theorems/d571269e-0979-4ddf-806d-1062d108210a
-- title:
--   Product Expansion: bad Bidirectional Local Pairs Encoding val
-- statement:
--   The Product Expansion construction uses the bad Bidirectional Local Pairs Encoding val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L590-L607
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L590-L607

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']

theorem QEC.Coding.ProductExpansion.badBidirectionalLocalPairsEncoding_val
    (d s m k : Nat)
    (p : badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) :
    badBidirectionalLocalPairsSumVal
      (badBidirectionalLocalPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d s m k p) = p.1 := by sorry
