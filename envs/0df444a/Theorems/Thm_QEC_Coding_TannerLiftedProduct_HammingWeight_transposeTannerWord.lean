-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_HammingWeight_transposeTannerWord
-- name    : QEC.Coding.TannerLiftedProduct.HammingWeight_transposeTannerWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:44:07.061203+00:00
-- url     : https://prove2.me/theorems/1f84cdcc-1e1a-4e1e-86b2-4d9b43f5646a
-- title:
--   Tanner Lifted Product: Hamming Weight transpose Tanner Word
-- statement:
--   Signed Tanner-factor transposition preserves the full Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L258-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L258-L278

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
omit [Fintype F] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.HammingWeight_transposeTannerWord
    (inverseDirection : W ≃ W)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    HammingWeight (transposeTannerWord inverseDirection z) = HammingWeight z := by sorry
