-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeTannerWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- name    : QEC.Coding.TannerLiftedProduct.transposeTannerWord_mem_middleCycleCode_of_mem_middleCocycleCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:12.997726+00:00
-- url     : https://prove2.me/theorems/9ee8b527-88de-4c77-8d9c-3a1738abc228
-- title:
--   Tanner Lifted Product: transpose Tanner Word mem middle Cycle Code of mem middle Cocycle Code
-- statement:
--   An original Tanner cocycle becomes a cycle for the product with exchanged
--   and inverse-direction-reindexed local matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L472-L490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L472-L490

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

theorem QEC.Coding.TannerLiftedProduct.transposeTannerWord_mem_middleCycleCode_of_mem_middleCocycleCode
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hz : z ∈ (chainComplex label h h').middleCocycleCode.carrier) :
    transposeTannerWord inverseDirection z ∈
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).middleCycleCode.carrier := by sorry
