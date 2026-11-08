-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_transposeTannerWord_apply
-- name    : QEC.Coding.TannerLiftedProduct.boundary1_transposeTannerWord_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:04.354802+00:00
-- url     : https://prove2.me/theorems/70146613-edba-4b5f-9d4f-67d8ab38474f
-- title:
--   Tanner Lifted Product: boundary1 transpose Tanner Word apply
-- statement:
--   Exchanging the Tanner factors intertwines the original second coboundary
--   with the first boundary of the exchanged product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L398-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L398-L468

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

theorem QEC.Coding.TannerLiftedProduct.boundary1_transposeTannerWord_apply
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G) :
    LiftedProduct.boundary1
        (data targetLabel (reindexColumns inverseDirection h')
          (reindexColumns inverseDirection h))
        (transposeTannerWord inverseDirection z)
        (transposeEdgeEquiv inverseDirection c2) =
      wordLinearMapTranspose (LiftedProduct.boundary2 (data label h h')) z c2 := by sorry
