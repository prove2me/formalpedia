-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_isLocallyMinimal_transposeTannerWord
-- name    : QEC.Coding.TannerLiftedProduct.isLocallyMinimal_transposeTannerWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:26.038333+00:00
-- url     : https://prove2.me/theorems/944c5fe9-eb59-4697-ba61-23c2b34e25dc
-- title:
--   Tanner Lifted Product: is Locally Minimal transpose Tanner Word
-- statement:
--   The Tanner Lifted Product construction uses the is Locally Minimal transpose Tanner Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L832-L851
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L832-L851

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

theorem QEC.Coding.TannerLiftedProduct.isLocallyMinimal_transposeTannerWord
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hzLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (verticalFiberCoboundaryMoves label h h') z) :
    LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves targetLabel
        (reindexColumns inverseDirection h')
        (reindexColumns inverseDirection h))
      (transposeTannerWord inverseDirection z) := by sorry
