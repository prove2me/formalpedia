-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedUnswapWord
-- name    : QEC.Coding.LiftedProduct.signedSwapWord_signedUnswapWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:28.096499+00:00
-- url     : https://prove2.me/theorems/fc1b52b6-b748-4e46-bdd4-634ec4bf42f1
-- title:
--   Lifted Product: signed Swap Word signed Unswap Word
-- statement:
--   The Lifted Product construction uses the signed Swap Word signed Unswap Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L60-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProductDuality.lean#L60-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.signedSwapWord_signedUnswapWord {F A B : Type*} [AddGroup F]
    (z : Word F (Sum B A)) :
    signedSwapWord (signedUnswapWord z) = z := by sorry
