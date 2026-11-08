-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_finrank_middleHomology_pos_of_local_ratio
-- name    : QEC.Coding.TannerLiftedProduct.finrank_middleHomology_pos_of_local_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:47:39.610223+00:00
-- url     : https://prove2.me/theorems/2ab14393-e931-4bdd-b630-f532a7539b60
-- title:
--   Tanner Lifted Product: finrank middle Homology pos of local ratio
-- statement:
--   A positive requested rate and the local-dimension ratio force the Tanner
--   middle homology, hence the encoded semantic space, to be nontrivial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L121-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerSemanticDistance.lean#L121-L145

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

theorem QEC.Coding.TannerLiftedProduct.finrank_middleHomology_pos_of_local_ratio
    (label : W → G) (h : Matrix R W F) (h' : Matrix R' W F)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hW : 0 < Fintype.card W)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    0 < Module.finrank F (chainComplex label h h').middleHomology := by sorry
