-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_transposeTannerWord
-- name    : QEC.Coding.TannerLiftedProduct.blockWeight_transposeTannerWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:41:32.026047+00:00
-- url     : https://prove2.me/theorems/493c6108-284c-4c90-bbfd-e284b12e277b
-- title:
--   Tanner Lifted Product: block Weight transpose Tanner Word
-- statement:
--   The Tanner Lifted Product construction uses the block Weight transpose Tanner Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L246-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L246-L253

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
omit [Fintype F] [DecidableEq G] [DecidableEq W] [DecidableEq R]
    [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.blockWeight_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    blockWeight (transposeTannerWord inverseDirection z) = blockWeight z := by sorry
