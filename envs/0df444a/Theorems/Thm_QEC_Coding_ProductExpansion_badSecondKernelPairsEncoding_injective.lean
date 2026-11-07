-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badSecondKernelPairsEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badSecondKernelPairsEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:24.134196+00:00
-- url     : https://prove2.me/theorems/391efc32-7ccf-42e6-8b4b-ded6415975ff
-- title:
--   Product Expansion: bad Second Kernel Pairs Encoding injective
-- statement:
--   The Product Expansion construction uses the bad Second Kernel Pairs Encoding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L154-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean#L154-L162

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [Fintype F] [DecidableEq W] hRFinite hR'Finite

theorem QEC.Coding.ProductExpansion.badSecondKernelPairsEncoding_injective (d : Nat) :
    Function.Injective
      (badSecondKernelPairsEncoding
        (F := F) (W := W) (R := R) (R' := R') d) := by sorry
