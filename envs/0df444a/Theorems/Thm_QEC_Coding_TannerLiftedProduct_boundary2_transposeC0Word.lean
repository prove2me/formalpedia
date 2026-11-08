-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary2_transposeC0Word
-- name    : QEC.Coding.TannerLiftedProduct.boundary2_transposeC0Word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:22.771304+00:00
-- url     : https://prove2.me/theorems/bb4bf147-adbf-42df-a46f-5e5d16c2b3ba
-- title:
--   Tanner Lifted Product: boundary2 transpose C0 Word
-- statement:
--   The Tanner Lifted Product construction uses the boundary2 transpose C0 Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L664-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L664-L761

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

theorem QEC.Coding.TannerLiftedProduct.boundary2_transposeC0Word
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G)) :
    LiftedProduct.boundary2
        (data targetLabel (reindexColumns inverseDirection h')
          (reindexColumns inverseDirection h))
        (transposeC0Word inverseDirection x) =
      transposeTannerWord inverseDirection
        (wordLinearMapTranspose (LiftedProduct.boundary1 (data label h h')) x) := by sorry
