-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
-- name    : QEC.Coding.TannerLiftedProduct.exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:52.487251+00:00
-- url     : https://prove2.me/theorems/2c0f2cb3-cb62-4d4a-9437-ace9a96a2e77
-- title:
--   Tanner Lifted Product: exists algebraic CSSMinimum Distance of finrank middle Homology pos
-- statement:
--   Positive Tanner middle-homology dimension makes at least one CSS logical
--   sector nonempty, so its algebraic CSS minimum is attained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L48-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L48-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_138d9bf296_24

theorem QEC.Coding.TannerLiftedProduct.exists_algebraicCSSMinimumDistance_of_finrank_middleHomology_pos
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (hPositive : 0 < Module.finrank F
      (chainComplex label h h').middleHomology) :
    ∃ dCSS : Nat,
      AlgebraicCSSMinimumDistance
        (chainComplex label h h').firstCoboundaryCheckCode
        (chainComplex label h h').middleBoundaryCode dCSS := by sorry
