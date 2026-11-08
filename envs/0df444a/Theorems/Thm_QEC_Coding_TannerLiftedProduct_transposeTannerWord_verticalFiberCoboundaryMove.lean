-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeTannerWord_verticalFiberCoboundaryMove
-- name    : QEC.Coding.TannerLiftedProduct.transposeTannerWord_verticalFiberCoboundaryMove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:41:08.480039+00:00
-- url     : https://prove2.me/theorems/a7e91a32-dd3e-4121-90df-010048a09a5b
-- title:
--   Tanner Lifted Product: transpose Tanner Word vertical Fiber Coboundary Move
-- statement:
--   The Tanner Lifted Product construction uses the transpose Tanner Word vertical Fiber Coboundary Move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L765-L782
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L765-L782

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

theorem QEC.Coding.TannerLiftedProduct.transposeTannerWord_verticalFiberCoboundaryMove
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (edge : VerticalEdgeIndex W G) (u : Word F R) :
    transposeTannerWord inverseDirection
        (wordLinearMapTranspose (chainComplex label h h').boundary1
          (verticalFiberCochain edge u)) =
      (chainComplex targetLabel (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h)).boundary2
        (horizontalFiberChain
          (transposeVerticalEdge inverseDirection edge) u) := by sorry
