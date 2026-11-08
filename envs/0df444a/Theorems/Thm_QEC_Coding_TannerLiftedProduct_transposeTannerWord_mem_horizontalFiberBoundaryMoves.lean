-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_transposeTannerWord_mem_horizontalFiberBoundaryMoves
-- name    : QEC.Coding.TannerLiftedProduct.transposeTannerWord_mem_horizontalFiberBoundaryMoves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:45:07.431342+00:00
-- url     : https://prove2.me/theorems/9e36b79f-552e-47a3-bc64-2745c2d3f6e5
-- title:
--   Tanner Lifted Product: transpose Tanner Word mem horizontal Fiber Boundary Moves
-- statement:
--   The Tanner Lifted Product construction uses the transpose Tanner Word mem horizontal Fiber Boundary Moves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L786-L803
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L786-L803

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

theorem QEC.Coding.TannerLiftedProduct.transposeTannerWord_mem_horizontalFiberBoundaryMoves
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (m : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hm : m ∈ verticalFiberCoboundaryMoves label h h') :
    transposeTannerWord inverseDirection m ∈
      horizontalFiberBoundaryMoves targetLabel
        (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h) := by sorry
