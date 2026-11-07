-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badFirstImagePairsEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badFirstImagePairsEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:05.347967+00:00
-- url     : https://prove2.me/theorems/b926640d-29f0-4766-bdcd-96f69aa6cbbb
-- title:
--   Product Expansion: bad First Image Pairs Encoding injective
-- statement:
--   The Product Expansion construction uses the bad First Image Pairs Encoding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L136-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L136-L144

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [Fintype F] [DecidableEq W] hR'Finite

theorem QEC.Coding.ProductExpansion.badFirstImagePairsEncoding_injective (d : Nat) :
    Function.Injective
      (badFirstImagePairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by sorry
