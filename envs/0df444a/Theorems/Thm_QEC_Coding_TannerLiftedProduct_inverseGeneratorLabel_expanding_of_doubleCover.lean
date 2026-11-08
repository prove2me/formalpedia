-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_inverseGeneratorLabel_expanding_of_doubleCover
-- name    : QEC.Coding.TannerLiftedProduct.inverseGeneratorLabel_expanding_of_doubleCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:42:59.440562+00:00
-- url     : https://prove2.me/theorems/d12c9254-b975-44ba-95ae-dedb165364a0
-- title:
--   Tanner Lifted Product: inverse Generator Label expanding of double Cover
-- statement:
--   The Tanner Lifted Product construction uses the inverse Generator Label expanding of double Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L982-L989
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerTranspose.lean#L982-L989

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq W]
    [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.inverseGeneratorLabel_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph (inverseGeneratorLabel label)) radius lambda := by sorry
