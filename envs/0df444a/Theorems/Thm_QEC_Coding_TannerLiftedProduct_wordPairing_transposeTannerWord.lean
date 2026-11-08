-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_wordPairing_transposeTannerWord
-- name    : QEC.Coding.TannerLiftedProduct.wordPairing_transposeTannerWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:29.635388+00:00
-- url     : https://prove2.me/theorems/ea4bccb3-04d2-4ab3-9698-b0b63490f25a
-- title:
--   Tanner Lifted Product: word Pairing transpose Tanner Word
-- statement:
--   The Tanner Lifted Product construction uses the word Pairing transpose Tanner Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L543-L561
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L543-L561

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq F] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.wordPairing_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (y : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G)) :
    wordPairing (transposeTannerWord inverseDirection z) y =
      wordPairing z (transposeTannerWord inverseDirection.symm y) := by sorry
