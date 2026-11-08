-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_algebraicCSSMinimumDistance_le_semanticPresentation_distance
-- name    : QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_le_semanticPresentation_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:43:14.473552+00:00
-- url     : https://prove2.me/theorems/f853b48a-55b6-4f66-b73e-b059826b109d
-- title:
--   Tanner Lifted Product: algebraic CSSMinimum Distance le semantic Presentation distance
-- statement:
--   The attained algebraic CSS minimum lower-bounds the actual semantic
--   distance of the Tanner finite-qudit presentation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L87-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L87-L100

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

theorem QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_le_semanticPresentation_distance
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (dCSS : Nat)
    (hMinimum : AlgebraicCSSMinimumDistance
      (chainComplex label h h').firstCoboundaryCheckCode
      (chainComplex label h h').middleBoundaryCode dCSS) :
    dCSS ≤ (semanticPresentation label h h').distance := by sorry
