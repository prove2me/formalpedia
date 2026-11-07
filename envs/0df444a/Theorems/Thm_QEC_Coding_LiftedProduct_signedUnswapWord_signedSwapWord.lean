-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedUnswapWord_signedSwapWord
-- name    : QEC.Coding.LiftedProduct.signedUnswapWord_signedSwapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:46.134468+00:00
-- url     : https://prove2.me/theorems/12926fb9-1322-4171-8a7d-9143804ee188
-- title:
--   Lifted Product: signed Unswap Word signed Swap Word
-- statement:
--   The Lifted Product construction uses the signed Unswap Word signed Swap Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L54-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L54-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedUnswapWord_signedSwapWord {F A B : Type*} [AddGroup F]
    (z : Word F (Sum A B)) :
    signedUnswapWord (signedSwapWord z) = z := by sorry
