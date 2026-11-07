-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badBidirectionalLocalPairsEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badBidirectionalLocalPairsEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:25.747465+00:00
-- url     : https://prove2.me/theorems/7cbbb3ad-4725-4c10-91a9-db0e0825d7ad
-- title:
--   Product Expansion: bad Bidirectional Local Pairs Encoding injective
-- statement:
--   The six-event encoding is injective because every branch retains its
--   underlying matrix pair.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L611-L619
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L611-L619

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']

theorem QEC.Coding.ProductExpansion.badBidirectionalLocalPairsEncoding_injective
    (d s m k : Nat) :
    Function.Injective
      (badBidirectionalLocalPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d s m k) := by sorry
