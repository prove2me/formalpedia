-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_verticalFiberCoboundaryMove_of_mem_horizontal
-- name    : QEC.Coding.TannerLiftedProduct.exists_verticalFiberCoboundaryMove_of_mem_horizontal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:51.14177+00:00
-- url     : https://prove2.me/theorems/0e96c944-9321-4abf-bcf9-32f712193a3d
-- title:
--   Tanner Lifted Product: exists vertical Fiber Coboundary Move of mem horizontal
-- statement:
--   The Tanner Lifted Product construction uses the exists vertical Fiber Coboundary Move of mem horizontal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L807-L828
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L807-L828

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

theorem QEC.Coding.TannerLiftedProduct.exists_verticalFiberCoboundaryMove_of_mem_horizontal
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (m' : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R') W W (Fin 2 × R) G))
    (hm' : m' ∈ horizontalFiberBoundaryMoves targetLabel
      (reindexColumns inverseDirection h')
      (reindexColumns inverseDirection h)) :
    ∃ m ∈ verticalFiberCoboundaryMoves label h h',
      transposeTannerWord inverseDirection m = m' := by sorry
