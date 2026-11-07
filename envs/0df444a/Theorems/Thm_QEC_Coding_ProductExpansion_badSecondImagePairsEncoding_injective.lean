-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badSecondImagePairsEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badSecondImagePairsEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:17.059038+00:00
-- url     : https://prove2.me/theorems/f48ab1af-b3b5-49ee-a527-ab843ebd72e3
-- title:
--   Product Expansion: bad Second Image Pairs Encoding injective
-- statement:
--   The Product Expansion construction uses the bad Second Image Pairs Encoding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L172-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L172-L180

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [Fintype F] [DecidableEq W] hRFinite

theorem QEC.Coding.ProductExpansion.badSecondImagePairsEncoding_injective (d : Nat) :
    Function.Injective
      (badSecondImagePairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by sorry
